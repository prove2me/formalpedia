-- Prove2me | solution 1 for TermCycDich.lemma_3_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:50:11.679848+00:00
-- url     : https://prove2.me/submissions/68018184-50c7-4889-ac61-4a06a115ae6c

import Mathlib
import Definitions.Def_TermCycDich_IsRCycle
import Definitions.Def_TermCycDich_IsMesh

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TermCycDich.L310

open SimpleGraph Classical

variable {V : Type} {G : SimpleGraph V}


/-! ### Path splitting helpers -/

theorem take_drop_inter {u v w x : V} {p : G.Walk u v} (hp : p.IsPath) (h : w ∈ p.support)
    (h1 : x ∈ (p.takeUntil w h).support) (h2 : x ∈ (p.dropUntil w h).support) : x = w := by
  have hnd := hp.support_nodup
  rw [← p.take_spec h, Walk.support_append] at hnd
  have hdisj := (List.nodup_append.1 hnd).2.2
  by_contra hne
  have h2' : x ∈ (p.dropUntil w h).support.tail := by
    rw [← Walk.cons_tail_support (p.dropUntil w h)] at h2 -- support = w :: tail
    rcases List.mem_cons.1 h2 with h3 | h3
    · exact absurd h3 hne
    · exact h3
  exact hdisj x h1 x h2' rfl

theorem isPath_append_of {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (hp : p.IsPath)
    (hq : q.IsPath) (h : ∀ x ∈ p.support, x ∈ q.support → x = v) : (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.sublist (List.tail_sublist _), ?_⟩
  intro a ha b hb hab
  subst hab
  have hav : a = v := h a ha (List.mem_of_mem_tail hb)
  subst hav
  have := hq.support_nodup
  rw [← Walk.cons_tail_support q] at this
  exact (List.nodup_cons.1 this).1 hb


/-! ### Assembly: leaves of `O` joined by disjoint paths give a union of cycles -/

/-- the graph traced by the pieces -/
def pieces {x y : Fin 3 → V} (w : ∀ k, G.Walk (x k) (y k)) : SimpleGraph V :=
  ⨆ k, (w k).toSubgraph.spanningCoe

theorem pieces_adj {x y : Fin 3 → V} (w : ∀ k, G.Walk (x k) (y k)) (a b : V) :
    (pieces w).Adj a b ↔ ∃ k, (w k).toSubgraph.Adj a b := by
  simp only [pieces, iSup_adj, Subgraph.spanningCoe_adj]

theorem piece_nbrs_start {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hab : a ≠ b) :
    (p.toSubgraph.spanningCoe.neighborSet a) = {p.snd} := by
  have := hp.neighborSet_toSubgraph_startpoint (Walk.not_nil_of_ne hab)
  rw [← this]; ext; simp

theorem piece_nbrs_end {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hab : a ≠ b) :
    (p.toSubgraph.spanningCoe.neighborSet b) = {p.penultimate} := by
  have := hp.neighborSet_toSubgraph_endpoint (Walk.not_nil_of_ne hab)
  rw [← this]; ext; simp

theorem piece_nbrs_internal {a b v : V} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support)
    (ha : v ≠ a) (hb : v ≠ b) : (p.toSubgraph.spanningCoe.neighborSet v).ncard = 2 := by
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.1 hv
  have h0 : i ≠ 0 := by rintro rfl; exact ha (Walk.getVert_zero p)
  have hl : i < p.length := by
    rcases Nat.lt_or_ge i p.length with h | h
    · exact h
    · exact absurd (by rw [show i = p.length by omega, Walk.getVert_length]) hb
  have := hp.ncard_neighborSet_toSubgraph_internal_eq_two h0 hl
  rw [← this]; congr 1

theorem nbrs_of_not_mem {a b v : V} (p : G.Walk a b) (hv : v ∉ p.support) :
    p.toSubgraph.spanningCoe.neighborSet v = ∅ := by
  ext z
  simp only [mem_neighborSet, Subgraph.spanningCoe_adj, Set.mem_empty_iff_false, iff_false]
  intro h
  exact hv (Walk.mem_support_of_adj_toSubgraph h)

theorem assembly [Finite V] (O : SimpleGraph V) (Lf : V → Prop)
    (hleaf : ∀ v, Lf v → (O.neighborSet v).ncard = 1)
    (hother : ∀ v, ¬ Lf v → O.neighborSet v = ∅ ∨ (O.neighborSet v).ncard = 2)
    (x y : Fin 3 → V) (w : ∀ k, G.Walk (x k) (y k)) (hw : ∀ k, (w k).IsPath)
    (hxy : ∀ k, x k ≠ y k)
    (hdisj : ∀ k k', k ≠ k' → ∀ v, v ∈ (w k).support → v ∉ (w k').support)
    (hends : ∀ k, Lf (x k) ∧ Lf (y k))
    (hint : ∀ k v, v ∈ (w k).support → v ≠ x k → v ≠ y k → O.neighborSet v = ∅)
    (hcover : ∀ v, Lf v → ∃ k, v = x k ∨ v = y k)
    (hedge : ∀ k a b, (w k).toSubgraph.Adj a b → ¬ O.Adj a b) :
    (O ⊔ pieces w).IsCycles := by
  intro v _
  have hfin : ∀ (H : SimpleGraph V), (H.neighborSet v).Finite := fun H => Set.toFinite _
  rw [neighborSet_sup]
  -- piece neighbourhoods
  have hpn : (pieces w).neighborSet v = ⋃ k, (w k).toSubgraph.spanningCoe.neighborSet v := by
    ext z; simp [pieces_adj]
  by_cases hin : ∃ k, v ∈ (w k).support
  · obtain ⟨k, hk⟩ := hin
    have hothers : ∀ k', k' ≠ k → (w k').toSubgraph.spanningCoe.neighborSet v = ∅ :=
      fun k' hk' => nbrs_of_not_mem _ (hdisj k k' (Ne.symm hk') v hk)
    have hpk : (pieces w).neighborSet v = (w k).toSubgraph.spanningCoe.neighborSet v := by
      rw [hpn]; ext z; simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨k', hz⟩
        by_cases hkk : k' = k
        · subst hkk; exact hz
        · rw [hothers k' hkk] at hz; exact hz.elim
      · intro hz; exact ⟨k, hz⟩
    rw [hpk]
    have hdj : Disjoint (O.neighborSet v) ((w k).toSubgraph.spanningCoe.neighborSet v) := by
      rw [Set.disjoint_left]
      intro z h1 h2
      exact hedge k v z h2 h1
    rw [Set.ncard_union_eq hdj (hfin _) (Set.toFinite _)]
    by_cases hx : v = x k
    · subst hx
      rw [hleaf _ (hends k).1, piece_nbrs_start _ (hw k) (hxy k)]; simp
    by_cases hy : v = y k
    · subst hy
      rw [hleaf _ (hends k).2, piece_nbrs_end _ (hw k) (hxy k)]; simp
    rw [hint k v hk hx hy, piece_nbrs_internal _ (hw k) hk hx hy]; simp
  · push Not at hin
    have hpk : (pieces w).neighborSet v = ∅ := by
      rw [hpn]; ext z; simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
      rintro ⟨k, hz⟩; rw [nbrs_of_not_mem _ (hin k)] at hz; exact hz
    have hnl : ¬ Lf v := by
      intro hl
      obtain ⟨k, hk | hk⟩ := hcover v hl
      · exact hin k (by rw [hk]; exact Walk.start_mem_support _)
      · exact hin k (by rw [hk]; exact Walk.end_mem_support _)
    rw [hpk, Set.union_empty]
    rename_i hne
    rw [neighborSet_sup, hpk, Set.union_empty] at hne
    rcases hother v hnl with h | h
    · rw [h] at hne; exact absurd hne Set.not_nonempty_empty
    · exact h


/-! ### From a connected union of cycles to a cycle walk -/

theorem extract_cycle [Finite V] (N : SimpleGraph V) (hNG : N ≤ G) (hcyc : N.IsCycles) (r : V)
    (hr : (N.neighborSet r).Nonempty)
    (hconn : ∀ v, (N.neighborSet v).Nonempty → N.Reachable r v) :
    ∃ C' : G.Walk r r, C'.IsCycle ∧ ∀ v, v ∈ C'.support ↔ (N.neighborSet v).Nonempty := by
  obtain ⟨p, hp, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := N.connectedComponentMk r) (v := r) rfl hr
  refine ⟨p.mapLe hNG, (Walk.isCycle_mapLe hNG).2 hp, fun v => ?_⟩
  rw [Walk.support_mapLe_eq_support, ← Walk.mem_verts_toSubgraph, hverts,
    ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  constructor
  · intro h
    have hrv : N.Reachable r v := h.symm
    by_cases hvr : v = r
    · subst hvr; exact hr
    · obtain ⟨q⟩ := hrv
      have hq : ¬ q.reverse.Nil := Walk.not_nil_of_ne hvr
      exact ⟨q.reverse.snd, q.reverse.adj_snd hq⟩
  · intro h; exact (hconn v h).symm

/-- the vertex sets are reachable from the root, given that leaves are -/
theorem assembly_connected (O : SimpleGraph V) (Lf : V → Prop) (x y : Fin 3 → V)
    (w : ∀ k, G.Walk (x k) (y k)) (hends : ∀ k, Lf (x k) ∧ Lf (y k)) (r : V)
    (hOroot : ∀ v, (O.neighborSet v).Nonempty → ∃ l, Lf l ∧ O.Reachable l v)
    (hleaves : ∀ l, Lf l → (O ⊔ pieces w).Reachable r l) :
    ∀ v, ((O ⊔ pieces w).neighborSet v).Nonempty → (O ⊔ pieces w).Reachable r v := by
  intro v hv
  rw [neighborSet_sup] at hv
  obtain ⟨z, hz | hz⟩ := hv
  · obtain ⟨l, hl, hlv⟩ := hOroot v ⟨z, hz⟩
    exact (hleaves l hl).trans (hlv.mono le_sup_left)
  · rw [mem_neighborSet, pieces_adj] at hz
    obtain ⟨k, hk⟩ := hz
    have hvs : v ∈ (w k).support := Walk.mem_support_of_adj_toSubgraph hk
    -- the prefix of the piece up to `v` lives in the pieces graph
    have hle : (w k).toSubgraph.spanningCoe ≤ O ⊔ pieces w := by
      intro a b hab
      exact Or.inr ((pieces_adj w a b).2 ⟨k, hab⟩)
    have hreach : ((w k).toSubgraph.spanningCoe).Reachable (x k) v := by
      have := (w k).toSubgraph_connected.preconnected ⟨x k, (w k).start_mem_verts_toSubgraph⟩
        ⟨v, (Walk.mem_verts_toSubgraph _).2 hvs⟩
      obtain ⟨q⟩ := this
      let f : (w k).toSubgraph.coe →g (w k).toSubgraph.spanningCoe := ⟨Subtype.val, fun h => h⟩
      exact ⟨q.map f⟩
    exact (hleaves _ (hends k).1).trans (hreach.mono hle)


/-! ### Six points -/

/-- adjacency of the extra pairs -/
def pairAdj (ps : List (Fin 6 × Fin 6)) (i j : Fin 6) : Bool :=
  ps.any (fun p => (p.1 == i && p.2 == j) || (p.1 == j && p.2 == i))

def step (lab : Fin 6 → ℕ) (ps : List (Fin 6 × Fin 6)) (S : Fin 6 → Bool) : Fin 6 → Bool :=
  fun j => S j || (List.finRange 6).any (fun i => S i && (lab i == lab j || pairAdj ps i j))

def closure (lab : Fin 6 → ℕ) (ps : List (Fin 6 × Fin 6)) : Fin 6 → Bool :=
  (step lab ps)^[5] (fun i => i == 0)

def conn (lab : Fin 6 → ℕ) (ps : List (Fin 6 × Fin 6)) : Bool :=
  (List.finRange 6).all (closure lab ps)

def noSing (lab : Fin 6 → ℕ) : Bool :=
  (List.finRange 6).all (fun i => (List.finRange 6).any (fun j => i != j && lab i == lab j))

-- points: 0 = t0, 1 = d0, 2 = t1, 3 = d1, 4 = t2, 5 = d2
def pQ : List (Fin 6 × Fin 6) := [(0, 1), (2, 3), (4, 5)]
def pA : List (Fin 6 × Fin 6) := [(0, 1), (2, 4), (3, 5)]
def pB : List (Fin 6 × Fin 6) := [(0, 5), (2, 4), (1, 3)]
def pC : List (Fin 6 × Fin 6) := [(0, 2), (4, 1), (3, 5)]

def labOf (l1 : Fin 2) (l2 : Fin 3) (l3 : Fin 4) (l4 : Fin 5) (l5 : Fin 6) : Fin 6 → ℕ :=
  ![0, l1, l2, l3, l4, l5]

theorem six_points : ∀ (l1 : Fin 2) (l2 : Fin 3) (l3 : Fin 4) (l4 : Fin 5) (l5 : Fin 6),
    noSing (labOf l1 l2 l3 l4 l5) = true → conn (labOf l1 l2 l3 l4 l5) pQ = true →
    (conn (labOf l1 l2 l3 l4 l5) pA || conn (labOf l1 l2 l3 l4 l5) pB ||
      conn (labOf l1 l2 l3 l4 l5) pC) = true := by
  decide


theorem closure_closed : ∀ (l1 : Fin 2) (l2 : Fin 3) (l3 : Fin 4) (l4 : Fin 5) (l5 : Fin 6)
    (i j : Fin 6), closure (labOf l1 l2 l3 l4 l5) pQ i = true →
    (labOf l1 l2 l3 l4 l5 i == labOf l1 l2 l3 l4 l5 j || pairAdj pQ i j) = true →
    closure (labOf l1 l2 l3 l4 l5) pQ j = true := by
  decide

theorem labOf_exists (lab : Fin 6 → ℕ) (h0 : lab 0 = 0) (hle : ∀ k, lab k ≤ k) :
    ∃ (l1 : Fin 2) (l2 : Fin 3) (l3 : Fin 4) (l4 : Fin 5) (l5 : Fin 6), labOf l1 l2 l3 l4 l5 = lab := by
  refine ⟨⟨lab 1, by have := hle 1; simp at this; omega⟩, ⟨lab 2, by have := hle 2; simp at this; omega⟩,
    ⟨lab 3, by have := hle 3; simp at this; omega⟩, ⟨lab 4, by have := hle 4; simp at this; omega⟩,
    ⟨lab 5, by have := hle 5; simp at this; omega⟩, ?_⟩
  funext k; fin_cases k <;> simp [labOf, h0]

theorem six_points' (lab : Fin 6 → ℕ) (h0 : lab 0 = 0) (hle : ∀ k, lab k ≤ k)
    (hns : noSing lab = true) (hq : conn lab pQ = true) :
    (conn lab pA || conn lab pB || conn lab pC) = true := by
  obtain ⟨l1, l2, l3, l4, l5, rfl⟩ := labOf_exists lab h0 hle
  exact six_points l1 l2 l3 l4 l5 hns hq

theorem closure_closed' (lab : Fin 6 → ℕ) (h0 : lab 0 = 0) (hle : ∀ k, lab k ≤ k) (i j : Fin 6)
    (hi : closure lab pQ i = true) (h : (lab i == lab j || pairAdj pQ i j) = true) :
    closure lab pQ j = true := by
  obtain ⟨l1, l2, l3, l4, l5, rfl⟩ := labOf_exists lab h0 hle
  exact closure_closed l1 l2 l3 l4 l5 i j hi h

/-- forward bridge: the closure only reaches points reachable in `H` -/
theorem closure_reach {V : Type} (H : SimpleGraph V) (ℓ : Fin 6 → V) (lab : Fin 6 → ℕ)
    (ps : List (Fin 6 × Fin 6)) (hlab : ∀ i j, lab i = lab j → H.Reachable (ℓ i) (ℓ j))
    (hps : ∀ i j, pairAdj ps i j = true → H.Reachable (ℓ i) (ℓ j)) :
    ∀ n j, ((step lab ps)^[n] (fun i => i == 0)) j = true → H.Reachable (ℓ 0) (ℓ j) := by
  intro n
  induction n with
  | zero => intro j hj; simp at hj; subst hj; exact Reachable.refl _
  | succ n ih =>
    intro j hj
    rw [Function.iterate_succ_apply'] at hj
    simp only [step, Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and,
      Bool.and_eq_true, beq_iff_eq] at hj
    rcases hj with hj | ⟨i, hi, hij | hij⟩
    · exact ih j hj
    · exact (ih i hi).trans (hlab i j hij)
    · exact (ih i hi).trans (hps i j hij)

theorem conn_reach {V : Type} (H : SimpleGraph V) (ℓ : Fin 6 → V) (lab : Fin 6 → ℕ)
    (ps : List (Fin 6 × Fin 6)) (hlab : ∀ i j, lab i = lab j → H.Reachable (ℓ i) (ℓ j))
    (hps : ∀ i j, pairAdj ps i j = true → H.Reachable (ℓ i) (ℓ j)) (hc : conn lab ps = true) :
    ∀ j, H.Reachable (ℓ 0) (ℓ j) := by
  intro j
  simp only [conn, List.all_eq_true, List.mem_finRange, true_implies] at hc
  exact closure_reach H ℓ lab ps hlab hps 5 j (hc j)

theorem col_pair : ∀ i j : Fin 6, (![0, 0, 1, 1, 2, 2] : Fin 6 → Fin 3) i = ![0, 0, 1, 1, 2, 2] j →
    i = j ∨ pairAdj pQ i j = true := by decide

theorem closure_zero (lab : Fin 6 → ℕ) (ps : List (Fin 6 × Fin 6)) : closure lab ps 0 = true := by
  have : ∀ n, ((step lab ps)^[n] (fun i => i == 0)) 0 = true := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply']; simp [step, ih]
  exact this 5

/-- Bundled data extracted from a `(4 × 3)`-mesh. -/
structure MD (P : Fin 4 → G.Subgraph) (Q : Fin 3 → G.Subgraph) where
  tq : Fin 3 → V
  dq : Fin 3 → V
  qw : ∀ j, G.Walk (tq j) (dq j)
  qpath : ∀ j, (qw j).IsPath
  qsub : ∀ j, (qw j).toSubgraph = Q j
  tq_mem : ∀ j, tq j ∈ (P 0).verts
  dq_mem : ∀ j, dq j ∈ (P 3).verts
  qend : ∀ j x, x ∈ (qw j).support → x ∈ (P 0).verts ∨ x ∈ (P 3).verts → x = tq j ∨ x = dq j
  sp : Fin 4 → V
  ep : Fin 4 → V
  pw : ∀ i, G.Walk (sp i) (ep i)
  ppath : ∀ i, (pw i).IsPath
  psub : ∀ i, (pw i).toSubgraph = P i
  sp_mem : ∀ i, sp i ∈ (Q 0).verts
  ep_mem : ∀ i, ep i ∈ (Q 2).verts
  pend : ∀ i x, x ∈ (pw i).support → x ∈ (Q 0).verts ∨ x ∈ (Q 2).verts → x = sp i ∨ x = ep i
  Pdisj : Pairwise (fun i i' => Disjoint (P i).verts (P i').verts)
  Qdisj : Pairwise (fun j j' => Disjoint (Q j).verts (Q j').verts)

theorem md_of_mesh {P : Fin 4 → G.Subgraph} {Q : Fin 3 → G.Subgraph}
    (hM : IsMesh (n := 2) (m := 1) P Q) : Nonempty (MD P Q) := by
  obtain ⟨hPd, hQd, -, hPo, hQo⟩ := hM
  choose sp ep pw hpp hps hsp hep hpend _ using hPo
  choose tq dq qw hqp hqs htq hdq hqend _ using hQo
  exact ⟨MD.mk tq dq qw hqp hqs htq hdq hqend sp ep pw hpp hps hsp hep hpend hPd hQd⟩

namespace MD
variable {P : Fin 4 → G.Subgraph} {Q : Fin 3 → G.Subgraph} (D : MD P Q)

theorem memQ {j x} : x ∈ (Q j).verts ↔ x ∈ (D.qw j).support := by
  rw [← D.qsub j, Walk.mem_verts_toSubgraph]
theorem memP {i x} : x ∈ (P i).verts ↔ x ∈ (D.pw i).support := by
  rw [← D.psub i, Walk.mem_verts_toSubgraph]

theorem tq_memQ (j) : D.tq j ∈ (Q j).verts := D.memQ.2 (Walk.start_mem_support _)
theorem dq_memQ (j) : D.dq j ∈ (Q j).verts := D.memQ.2 (Walk.end_mem_support _)
theorem sp_memP (i) : D.sp i ∈ (P i).verts := D.memP.2 (Walk.start_mem_support _)
theorem ep_memP (i) : D.ep i ∈ (P i).verts := D.memP.2 (Walk.end_mem_support _)

include D in
theorem notP {i i' x} (h : i ≠ i') (hx : x ∈ (P i).verts) : x ∉ (P i').verts :=
  fun h' => Set.disjoint_left.1 (D.Pdisj h) hx h'
include D in
theorem notQ {j j' x} (h : j ≠ j') (hx : x ∈ (Q j).verts) : x ∉ (Q j').verts :=
  fun h' => Set.disjoint_left.1 (D.Qdisj h) hx h'

/-- the only vertex of `Q j` in `P 0` is its top `tq j` -/
theorem eq_tq {j x} (hx : x ∈ (Q j).verts) (h0 : x ∈ (P 0).verts) : x = D.tq j := by
  rcases D.qend j x (D.memQ.1 hx) (Or.inl h0) with h | h
  · exact h
  · exact absurd (h ▸ D.dq_mem j) (D.notP (by decide) h0)
theorem eq_dq {j x} (hx : x ∈ (Q j).verts) (h3 : x ∈ (P 3).verts) : x = D.dq j := by
  rcases D.qend j x (D.memQ.1 hx) (Or.inr h3) with h | h
  · exact absurd (h ▸ D.tq_mem j) (D.notP (by decide) h3)
  · exact h
theorem eq_sp {i x} (hx : x ∈ (P i).verts) (h0 : x ∈ (Q 0).verts) : x = D.sp i := by
  rcases D.pend i x (D.memP.1 hx) (Or.inl h0) with h | h
  · exact h
  · exact absurd (h ▸ D.ep_mem i) (D.notQ (by decide) h0)
theorem eq_ep {i x} (hx : x ∈ (P i).verts) (h2 : x ∈ (Q 2).verts) : x = D.ep i := by
  rcases D.pend i x (D.memP.1 hx) (Or.inr h2) with h | h
  · exact absurd (h ▸ D.sp_mem i) (D.notQ (by decide) h2)
  · exact h

theorem sp0 : D.sp 0 = D.tq 0 := (D.eq_sp (D.tq_mem 0) (D.tq_memQ 0)).symm
theorem ep0 : D.ep 0 = D.tq 2 := (D.eq_ep (D.tq_mem 2) (D.tq_memQ 2)).symm
theorem sp3 : D.sp 3 = D.dq 0 := (D.eq_sp (D.dq_mem 0) (D.dq_memQ 0)).symm
theorem ep3 : D.ep 3 = D.dq 2 := (D.eq_ep (D.dq_mem 2) (D.dq_memQ 2)).symm

end MD

/-! ### The cycle side -/

section CSide
variable [Fintype V] {P : Fin 4 → G.Subgraph} {Q : Fin 3 → G.Subgraph}

/-- the mesh -/
def Msh (P : Fin 4 → G.Subgraph) (Q : Fin 3 → G.Subgraph) : G.Subgraph := (⨆ i, P i) ⊔ (⨆ j, Q j)
def Cg {u : V} (C : G.Walk u u) : SimpleGraph V := C.toSubgraph.spanningCoe
def Qg (Q : Fin 3 → G.Subgraph) : SimpleGraph V := (⨆ j, Q j).spanningCoe
def Og {u : V} (C : G.Walk u u) (Q : Fin 3 → G.Subgraph) : SimpleGraph V := Cg C \ Qg Q
def Lf (D : MD P Q) (v : V) : Prop := ∃ j, v = D.tq j ∨ v = D.dq j

variable (D : MD P Q) {u : V} (C : G.Walk u u) (hC : C.IsCycle)
  (hCM : C.toSubgraph ⊓ Msh P Q = ⨆ j, Q j)
include hCM

theorem Q_le_C (j : Fin 3) {a b : V} (h : (Q j).Adj a b) : C.toSubgraph.Adj a b := by
  have : (⨆ j, Q j).Adj a b := Subgraph.iSup_adj.2 ⟨j, h⟩
  rw [← hCM, Subgraph.inf_adj] at this
  exact this.1

theorem Qv_C (j : Fin 3) {v : V} (h : v ∈ (Q j).verts) : v ∈ C.support := by
  have : v ∈ (⨆ j, Q j).verts := by rw [Subgraph.verts_iSup]; exact Set.mem_iUnion.2 ⟨j, h⟩
  rw [← hCM, Subgraph.verts_inf] at this
  exact (Walk.mem_verts_toSubgraph _).1 this.1

theorem CM_Q {v : V} (h1 : v ∈ C.support) (h2 : v ∈ (Msh P Q).verts) : ∃ j, v ∈ (Q j).verts := by
  have : v ∈ (C.toSubgraph ⊓ Msh P Q).verts := by
    rw [Subgraph.verts_inf]; exact ⟨(Walk.mem_verts_toSubgraph _).2 h1, h2⟩
  rw [hCM, Subgraph.verts_iSup] at this
  exact Set.mem_iUnion.1 this

theorem O_not_M {a b : V} (h : (Og C Q).Adj a b) : ¬ (Msh P Q).Adj a b := by
  intro hm
  simp only [Og, Cg, Qg, sdiff_adj, Subgraph.spanningCoe_adj] at h
  apply h.2
  rw [← hCM, Subgraph.inf_adj]
  exact ⟨h.1, hm⟩

omit hCM in
theorem Og_nbrs (v : V) : (Og C Q).neighborSet v = (Cg C).neighborSet v \ (Qg Q).neighborSet v := by
  ext z; simp [Og]

omit hCM in
theorem Qg_nbrs (j : Fin 3) {v : V} (hv : v ∈ (Q j).verts) :
    (Qg Q).neighborSet v = (D.qw j).toSubgraph.spanningCoe.neighborSet v := by
  ext z
  simp only [Qg, mem_neighborSet, Subgraph.spanningCoe_adj, Subgraph.iSup_adj, D.qsub]
  constructor
  · rintro ⟨j', h⟩
    by_cases hj : j' = j
    · subst hj; exact h
    · exact absurd (h.fst_mem) (D.notQ (Ne.symm hj) hv)
  · intro h; exact ⟨j, h⟩

omit hCM in
theorem Qg_nbrs_none {v : V} (hv : ∀ j, v ∉ (Q j).verts) : (Qg Q).neighborSet v = ∅ := by
  ext z
  simp only [Qg, mem_neighborSet, Subgraph.spanningCoe_adj, Subgraph.iSup_adj,
    Set.mem_empty_iff_false, iff_false, not_exists]
  intro j h; exact hv j h.fst_mem

theorem Qg_sub_Cg (v : V) : (Qg Q).neighborSet v ⊆ (Cg C).neighborSet v := by
  intro z hz
  simp only [Qg, mem_neighborSet, Subgraph.spanningCoe_adj, Subgraph.iSup_adj] at hz
  obtain ⟨j, h⟩ := hz
  exact Q_le_C C hCM j h

omit hCM in
theorem tq_ne_dq (j : Fin 3) : D.tq j ≠ D.dq j := fun h => D.notP (by decide) (D.tq_mem j) (h ▸ D.dq_mem j)

omit hCM in
theorem Cg_card (hC : C.IsCycle) {v : V} (hv : v ∈ C.support) : ((Cg C).neighborSet v).ncard = 2 := by
  have := hC.ncard_neighborSet_toSubgraph_eq_two hv
  rw [← this]; congr 1

omit hCM in
theorem Cg_empty {v : V} (hv : v ∉ C.support) : (Cg C).neighborSet v = ∅ := by
  simp only [Cg]; exact nbrs_of_not_mem C hv

include hC in
theorem O_leaf {v : V} (hv : Lf D v) : ((Og C Q).neighborSet v).ncard = 1 := by
  obtain ⟨j, hj⟩ := hv
  have hvQ : v ∈ (Q j).verts := by rcases hj with rfl | rfl; exact D.tq_memQ j; exact D.dq_memQ j
  have hvC := Qv_C C hCM j hvQ
  rw [Og_nbrs, Set.ncard_sdiff (Qg_sub_Cg C hCM v), Cg_card C hC hvC, Qg_nbrs D j hvQ]
  rcases hj with rfl | rfl
  · rw [piece_nbrs_start _ (D.qpath j) (tq_ne_dq D j)]; simp
  · rw [piece_nbrs_end _ (D.qpath j) (tq_ne_dq D j)]; simp

include hC in
theorem O_Qint {v : V} {j : Fin 3} (hvQ : v ∈ (Q j).verts) (h1 : v ≠ D.tq j) (h2 : v ≠ D.dq j) :
    (Og C Q).neighborSet v = ∅ := by
  have hvC := Qv_C C hCM j hvQ
  have hq2 : ((Qg Q).neighborSet v).ncard = 2 := by
    rw [Qg_nbrs D j hvQ]; exact piece_nbrs_internal _ (D.qpath j) (D.memQ.1 hvQ) h1 h2
  have heq : (Qg Q).neighborSet v = (Cg C).neighborSet v :=
    Set.eq_of_subset_of_ncard_le (Qg_sub_Cg C hCM v) (by rw [hq2, Cg_card C hC hvC])
      (Set.toFinite _)
  rw [Og_nbrs, heq, Set.sdiff_self]

include hC in
theorem O_other {v : V} (hv : ¬ Lf D v) :
    (Og C Q).neighborSet v = ∅ ∨ ((Og C Q).neighborSet v).ncard = 2 := by
  by_cases hvC : v ∈ C.support
  · by_cases hq : ∃ j, v ∈ (Q j).verts
    · left
      obtain ⟨j, hvQ⟩ := hq
      exact O_Qint D C hC hCM hvQ (fun h => hv ⟨j, Or.inl h⟩) (fun h => hv ⟨j, Or.inr h⟩)
    · right
      push Not at hq
      rw [Og_nbrs, Qg_nbrs_none hq, Set.sdiff_empty, Cg_card C hC hvC]
  · left; rw [Og_nbrs, Cg_empty C hvC, Set.empty_sdiff]

include hC in
theorem M_leaf {v : V} (hM : v ∈ (Msh P Q).verts) (hn : ((Og C Q).neighborSet v).Nonempty) :
    Lf D v := by
  by_contra hl
  have hvC : v ∈ C.support := by
    by_contra h
    rw [Og_nbrs, Cg_empty C h, Set.empty_sdiff] at hn
    exact Set.not_nonempty_empty hn
  obtain ⟨j, hvQ⟩ := CM_Q C hCM hvC hM
  rw [O_Qint D C hC hCM hvQ (fun h => hl ⟨j, Or.inl h⟩) (fun h => hl ⟨j, Or.inr h⟩)] at hn
  exact Set.not_nonempty_empty hn

omit hCM in
theorem reach_closed {H : SimpleGraph V} (S : Set V) (hS : ∀ a b, a ∈ S → H.Adj a b → b ∈ S)
    {a b : V} (h : H.Reachable a b) (ha : a ∈ S) : b ∈ S := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hS _ _ ha hadj)

omit hCM in
theorem Cg_reach {a b : V} (ha : a ∈ C.support) (hb : b ∈ C.support) : (Cg C).Reachable a b := by
  have := C.toSubgraph_connected.preconnected ⟨a, (Walk.mem_verts_toSubgraph _).2 ha⟩
    ⟨b, (Walk.mem_verts_toSubgraph _).2 hb⟩
  obtain ⟨q⟩ := this
  let f : C.toSubgraph.coe →g C.toSubgraph.spanningCoe := ⟨Subtype.val, fun h => h⟩
  exact ⟨q.map f⟩

omit hCM in
theorem nbrs_of_reach {H : SimpleGraph V} {a b : V} (h : H.Reachable a b) (hab : a ≠ b) :
    (H.neighborSet b).Nonempty := by
  obtain ⟨q⟩ := h
  have hq : ¬ q.reverse.Nil := Walk.not_nil_of_ne (Ne.symm hab)
  exact ⟨q.reverse.snd, q.reverse.adj_snd hq⟩

include hC in
theorem O_root {v : V} (hv : ((Og C Q).neighborSet v).Nonempty) :
    ∃ l, Lf D l ∧ (Og C Q).Reachable l v := by
  by_contra hno
  push Not at hno
  let K : Set V := {z | (Og C Q).Reachable v z}
  have hKne : ∀ z ∈ K, ((Og C Q).neighborSet z).Nonempty := by
    intro z hz
    by_cases hzv : v = z
    · subst hzv; exact hv
    · exact nbrs_of_reach hz hzv
  have hKleaf : ∀ z ∈ K, ¬ Lf D z := fun z hz hl => hno z hl hz.symm
  have hclosed : ∀ a b, a ∈ K → (Cg C).Adj a b → b ∈ K := by
    intro a b ha hab
    have h2 : ((Og C Q).neighborSet a).ncard = 2 := by
      rcases O_other D C hC hCM (hKleaf a ha) with h | h
      · exact absurd (h ▸ hKne a ha) Set.not_nonempty_empty
      · exact h
    have haC : a ∈ C.support := by
      by_contra h
      have := hKne a ha
      rw [Og_nbrs, Cg_empty C h, Set.empty_sdiff] at this
      exact Set.not_nonempty_empty this
    have heq : (Og C Q).neighborSet a = (Cg C).neighborSet a :=
      Set.eq_of_subset_of_ncard_le (by rw [Og_nbrs]; exact Set.sdiff_subset)
        (by rw [h2, Cg_card C hC haC]) (Set.toFinite _)
    have : b ∈ (Og C Q).neighborSet a := by rw [heq]; exact hab
    exact ha.trans (Adj.reachable this)
  have hvC : v ∈ C.support := by
    by_contra h
    rw [Og_nbrs, Cg_empty C h, Set.empty_sdiff] at hv
    exact Set.not_nonempty_empty hv
  have := reach_closed K hclosed (Cg_reach C hvC (Qv_C C hCM 0 (D.tq_memQ 0))) (Reachable.refl v)
  exact hKleaf _ this ⟨0, Or.inl rfl⟩

include hC in
theorem leaf_partner {l : V} (hl : Lf D l) : ∃ l', Lf D l' ∧ l' ≠ l ∧ (Og C Q).Reachable l l' := by
  let O := Og C Q
  let r : V → V → Prop := fun a b => O.Adj a b ∧ O.Reachable l a
  let O' : SimpleGraph V := SimpleGraph.fromRel r
  have hO' : ∀ a b, O'.Adj a b ↔ O.Adj a b ∧ O.Reachable l a := by
    intro a b
    simp only [O', SimpleGraph.fromRel_adj, r]
    constructor
    · rintro ⟨_, h | h⟩
      · exact h
      · exact ⟨h.1.symm, h.2.trans h.1.reachable⟩
    · intro h; exact ⟨h.1.ne, Or.inl h⟩
  have hdeg : ∀ a, O'.degree a = if O.Reachable l a then (O.neighborSet a).ncard else 0 := by
    intro a
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    split
    · rename_i h
      congr 1; ext b; simp only [mem_neighborSet, hO']; exact ⟨fun h' => h'.1, fun h' => ⟨h', h⟩⟩
    · rename_i h
      convert Set.ncard_empty V
      ext b; simp only [mem_neighborSet, hO', Set.mem_empty_iff_false, iff_false]
      exact fun h' => h h'.2
  have hodd : ∀ a, Odd (O'.degree a) ↔ O.Reachable l a ∧ Lf D a := by
    intro a
    rw [hdeg]
    split
    · rename_i h
      by_cases hla : Lf D a
      · simp only [h, hla, and_self, iff_true]; rw [O_leaf D C hC hCM hla]; decide
      · simp only [h, hla, and_false, iff_false]
        rcases O_other D C hC hCM hla with h' | h'
        · rw [h', Set.ncard_empty]; decide
        · rw [h']; decide
    · rename_i h; simp [h]
  have hev := O'.even_card_odd_degree_vertices
  have hmem : l ∈ Finset.univ.filter (fun a => Odd (O'.degree a)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hodd]; exact ⟨Reachable.refl l, hl⟩
  have hcard : 1 < (Finset.univ.filter (fun a => Odd (O'.degree a))).card := by
    obtain ⟨k, hk⟩ := hev
    have := Finset.card_pos.2 ⟨l, hmem⟩
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hodd] at ha hb
  by_cases hal : a = l
  · subst hal; exact ⟨b, hb.2, Ne.symm hab, hb.1⟩
  · exact ⟨a, ha.2, hal, ha.1⟩

/-! #### Leaves as six labelled points -/

def lv (D : MD P Q) : Fin 6 → V := ![D.tq 0, D.dq 0, D.tq 1, D.dq 1, D.tq 2, D.dq 2]
def col : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

omit hCM in
theorem lv_memQ (i : Fin 6) : lv D i ∈ (Q (col i)).verts := by
  fin_cases i
  · exact D.tq_memQ 0
  · exact D.dq_memQ 0
  · exact D.tq_memQ 1
  · exact D.dq_memQ 1
  · exact D.tq_memQ 2
  · exact D.dq_memQ 2

omit hCM in
theorem Lf_lv (i : Fin 6) : Lf D (lv D i) := by
  fin_cases i
  · exact ⟨0, Or.inl rfl⟩
  · exact ⟨0, Or.inr rfl⟩
  · exact ⟨1, Or.inl rfl⟩
  · exact ⟨1, Or.inr rfl⟩
  · exact ⟨2, Or.inl rfl⟩
  · exact ⟨2, Or.inr rfl⟩

omit hCM in
theorem Lf_iff {v : V} : Lf D v ↔ ∃ i, v = lv D i := by
  constructor
  · rintro ⟨j, h | h⟩ <;> fin_cases j
    · exact ⟨0, h⟩
    · exact ⟨2, h⟩
    · exact ⟨4, h⟩
    · exact ⟨1, h⟩
    · exact ⟨3, h⟩
    · exact ⟨5, h⟩
  · rintro ⟨i, rfl⟩; exact Lf_lv D i

omit hCM in
theorem leaf_col {v : V} (hl : Lf D v) {c : Fin 3} (hc : v ∈ (Q c).verts) :
    ∃ i, v = lv D i ∧ col i = c := by
  obtain ⟨i, rfl⟩ := (Lf_iff D).1 hl
  refine ⟨i, rfl, ?_⟩
  by_contra h
  exact D.notQ h (lv_memQ D i) hc

omit hCM in
theorem lv_inj : Function.Injective (lv D) := by
  intro i j h
  by_contra hij
  have hc : col i = col j := by
    by_contra hc; exact D.notQ hc (lv_memQ D i) (h ▸ lv_memQ D j)
  fin_cases i <;> fin_cases j <;> simp [col] at hc hij <;> simp [lv] at h
  all_goals first
    | exact tq_ne_dq D _ h
    | exact tq_ne_dq D _ h.symm

/-- the label of a leaf: the least index of a leaf in its `O`-component -/
noncomputable def labO (k : Fin 6) : ℕ :=
  ((Finset.univ.filter (fun m => (Og C Q).Reachable (lv D m) (lv D k))).min' ⟨k, by simp⟩ : Fin 6).val

omit hCM in
theorem labO_iff (i j : Fin 6) : labO D C i = labO D C j ↔ (Og C Q).Reachable (lv D i) (lv D j) := by
  constructor
  · intro h
    simp only [labO] at h
    have hi := Finset.min'_mem (Finset.univ.filter (fun m => (Og C Q).Reachable (lv D m) (lv D i)))
      ⟨i, by simp⟩
    have hj := Finset.min'_mem (Finset.univ.filter (fun m => (Og C Q).Reachable (lv D m) (lv D j)))
      ⟨j, by simp⟩
    rw [Fin.val_eq_val] at h
    rw [h] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hi.symm.trans hj
  · intro h
    simp only [labO]
    congr 1
    apply le_antisymm
    · apply Finset.min'_le
      have h1 := Finset.min'_mem (Finset.univ.filter (fun m => (Og C Q).Reachable (lv D m) (lv D j)))
        ⟨j, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
      exact h1.trans h.symm
    · apply Finset.min'_le
      have h1 := Finset.min'_mem (Finset.univ.filter (fun m => (Og C Q).Reachable (lv D m) (lv D i)))
        ⟨i, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
      exact h1.trans h

omit hCM in
theorem labO_le (k : Fin 6) : labO D C k ≤ k := by
  simp only [labO]
  have := Finset.min'_le (Finset.univ.filter (fun m => (Og C Q).Reachable (lv D m) (lv D k))) k
    (by simp)
  exact this

omit hCM in
theorem labO_zero : labO D C 0 = 0 := by
  have := labO_le D C 0; simp at this; exact this

include hC in
theorem labO_noSing : noSing (labO D C) = true := by
  simp only [noSing, List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true,
    Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, true_and]
  intro i
  obtain ⟨l', hl', hne, hr⟩ := leaf_partner D C hC hCM (Lf_lv D i)
  obtain ⟨j, rfl⟩ := (Lf_iff D).1 hl'
  refine ⟨j, fun h => hne (h ▸ rfl), (labO_iff D C i j).2 hr⟩

include hC in
theorem labO_connQ : conn (labO D C) pQ = true := by
  set S := closure (labO D C) pQ with hS
  have hcl : ∀ i j, S i = true → (labO D C i == labO D C j || pairAdj pQ i j) = true → S j = true :=
    closure_closed' _ (labO_zero D C) (labO_le D C)
  have hcol : ∀ i j, S i = true → col i = col j → S j = true := by
    intro i j hi hc
    rcases col_pair i j hc with rfl | h
    · exact hi
    · exact hcl i j hi (by simp [h])
  let U : Set V := {z | ∃ i, S i = true ∧ ((Og C Q).Reachable (lv D i) z ∨ z ∈ (Q (col i)).verts)}
  -- a vertex of `Q c` that is `O`-reachable from a leaf with true label is itself a true leaf
  have hstep : ∀ i z c, S i = true → (Og C Q).Reachable (lv D i) z → z ∈ (Q c).verts →
      ∃ k, z = lv D k ∧ col k = c ∧ S k = true := by
    intro i z c hi hr hz
    have hlz : Lf D z := by
      by_cases hzi : lv D i = z
      · rw [← hzi]; exact Lf_lv D i
      · refine M_leaf D C hC hCM ?_ (nbrs_of_reach hr hzi)
        simp only [Msh, Subgraph.verts_sup, Subgraph.verts_iSup]
        exact Or.inr (Set.mem_iUnion.2 ⟨c, hz⟩)
    obtain ⟨k, rfl, hk⟩ := leaf_col D hlz hz
    exact ⟨k, rfl, hk, hcl i k hi (by simp [(labO_iff D C i k).2 hr])⟩
  have hclosed : ∀ a b, a ∈ U → (Cg C).Adj a b → b ∈ U := by
    rintro a b ⟨i, hi, ha⟩ hab
    by_cases hq : (Qg Q).Adj a b
    · simp only [Qg, Subgraph.spanningCoe_adj, Subgraph.iSup_adj] at hq
      obtain ⟨j, hj⟩ := hq
      rcases ha with ha | ha
      · obtain ⟨k, rfl, hk, hSk⟩ := hstep i a j hi ha hj.fst_mem
        exact ⟨k, hSk, Or.inr (hk ▸ hj.snd_mem)⟩
      · have : j = col i := by
          by_contra h; exact D.notQ h hj.fst_mem ha
        subst this
        exact ⟨i, hi, Or.inr hj.snd_mem⟩
    · have hO : (Og C Q).Adj a b := by simp only [Og, sdiff_adj]; exact ⟨hab, hq⟩
      rcases ha with ha | ha
      · exact ⟨i, hi, Or.inl (ha.trans hO.reachable)⟩
      · have hlz : Lf D a := M_leaf D C hC hCM (by
          simp only [Msh, Subgraph.verts_sup, Subgraph.verts_iSup]
          exact Or.inr (Set.mem_iUnion.2 ⟨col i, ha⟩)) ⟨b, hO⟩
        obtain ⟨k, rfl, hk⟩ := leaf_col D hlz ha
        exact ⟨k, hcol i k hi hk.symm, Or.inl hO.reachable⟩
  have h0 : lv D 0 ∈ U := ⟨0, closure_zero _ _, Or.inl (Reachable.refl _)⟩
  simp only [conn, List.all_eq_true, List.mem_finRange, true_implies]
  intro j
  have hjC : lv D j ∈ C.support := Qv_C C hCM _ (lv_memQ D j)
  have h0C : lv D 0 ∈ C.support := Qv_C C hCM _ (lv_memQ D 0)
  obtain ⟨i, hi, hj⟩ := reach_closed U hclosed (Cg_reach C h0C hjC) h0
  rcases hj with hj | hj
  · exact hcl i j hi (by simp [(labO_iff D C i j).2 hj])
  · obtain ⟨k, hk, hck⟩ := leaf_col D (Lf_lv D j) hj
    have hjk := lv_inj D hk
    exact hcol i j hi (by rw [hjk]; exact hck.symm)

end CSide
/-! ### The rerouting pieces -/

section Pieces
variable {P : Fin 4 → G.Subgraph} {Q : Fin 3 → G.Subgraph} (D : MD P Q)

theorem not_mem_take_end {u v w : V} {p : G.Walk u v} (hp : p.IsPath) (h : w ∈ p.support)
    (hw : w ≠ v) : v ∉ (p.takeUntil w h).support := fun hv =>
  hw (take_drop_inter hp h hv (Walk.end_mem_support _)).symm

theorem not_mem_drop_start {u v w : V} {p : G.Walk u v} (hp : p.IsPath) (h : w ∈ p.support)
    (hw : w ≠ u) : u ∉ (p.dropUntil w h).support := fun hu =>
  hw (take_drop_inter hp h (Walk.start_mem_support _) hu).symm

namespace MD
def p0 : G.Walk (D.tq 0) (D.tq 2) := (D.pw 0).copy D.sp0 D.ep0
def p3 : G.Walk (D.dq 0) (D.dq 2) := (D.pw 3).copy D.sp3 D.ep3
theorem p0_path : D.p0.IsPath := by simp [p0, D.ppath 0]
theorem p3_path : D.p3.IsPath := by simp [p3, D.ppath 3]
theorem p0_supp {v : V} : v ∈ D.p0.support ↔ v ∈ (P 0).verts := by simp [p0, D.memP]
theorem p3_supp {v : V} : v ∈ D.p3.support ↔ v ∈ (P 3).verts := by simp [p3, D.memP]
theorem t1_mem : D.tq 1 ∈ D.p0.support := D.p0_supp.2 (D.tq_mem 1)
theorem d1_mem : D.dq 1 ∈ D.p3.support := D.p3_supp.2 (D.dq_mem 1)
theorem a_mem : D.sp 2 ∈ (D.qw 0).support := D.memQ.1 (D.sp_mem 2)
theorem b_mem : D.ep 2 ∈ (D.qw 2).support := D.memQ.1 (D.ep_mem 2)

noncomputable def P0a := D.p0.takeUntil _ D.t1_mem
noncomputable def P0b := D.p0.dropUntil _ D.t1_mem
noncomputable def P3a := D.p3.takeUntil _ D.d1_mem
noncomputable def P3b := D.p3.dropUntil _ D.d1_mem
noncomputable def Q0a := (D.qw 0).takeUntil _ D.a_mem
noncomputable def Q0b := (D.qw 0).dropUntil _ D.a_mem
noncomputable def Q2a := (D.qw 2).takeUntil _ D.b_mem
noncomputable def Q2b := (D.qw 2).dropUntil _ D.b_mem

theorem tq_ne {j j' : Fin 3} (h : j ≠ j') : D.tq j ≠ D.tq j' := fun e =>
  D.notQ h (D.tq_memQ j) (e ▸ D.tq_memQ j')
theorem dq_ne {j j' : Fin 3} (h : j ≠ j') : D.dq j ≠ D.dq j' := fun e =>
  D.notQ h (D.dq_memQ j) (e ▸ D.dq_memQ j')
theorem a_ne_t0 : D.sp 2 ≠ D.tq 0 := fun e => D.notP (by decide) (D.sp_memP 2) (e ▸ D.tq_mem 0)
theorem a_ne_d0 : D.sp 2 ≠ D.dq 0 := fun e => D.notP (by decide) (D.sp_memP 2) (e ▸ D.dq_mem 0)
theorem b_ne_t2 : D.ep 2 ≠ D.tq 2 := fun e => D.notP (by decide) (D.ep_memP 2) (e ▸ D.tq_mem 2)
theorem b_ne_d2 : D.ep 2 ≠ D.dq 2 := fun e => D.notP (by decide) (D.ep_memP 2) (e ▸ D.dq_mem 2)

-- supports of the segments
theorem P0a_sub {v : V} (h : v ∈ D.P0a.support) : v ∈ (P 0).verts :=
  D.p0_supp.1 (Walk.support_takeUntil_subset_support _ _ h)
theorem P0b_sub {v : V} (h : v ∈ D.P0b.support) : v ∈ (P 0).verts :=
  D.p0_supp.1 (Walk.support_dropUntil_subset_support _ _ h)
theorem P3a_sub {v : V} (h : v ∈ D.P3a.support) : v ∈ (P 3).verts :=
  D.p3_supp.1 (Walk.support_takeUntil_subset_support _ _ h)
theorem P3b_sub {v : V} (h : v ∈ D.P3b.support) : v ∈ (P 3).verts :=
  D.p3_supp.1 (Walk.support_dropUntil_subset_support _ _ h)
theorem Q0a_sub {v : V} (h : v ∈ D.Q0a.support) : v ∈ (Q 0).verts :=
  D.memQ.2 (Walk.support_takeUntil_subset_support _ _ h)
theorem Q0b_sub {v : V} (h : v ∈ D.Q0b.support) : v ∈ (Q 0).verts :=
  D.memQ.2 (Walk.support_dropUntil_subset_support _ _ h)
theorem Q2a_sub {v : V} (h : v ∈ D.Q2a.support) : v ∈ (Q 2).verts :=
  D.memQ.2 (Walk.support_takeUntil_subset_support _ _ h)
theorem Q2b_sub {v : V} (h : v ∈ D.Q2b.support) : v ∈ (Q 2).verts :=
  D.memQ.2 (Walk.support_dropUntil_subset_support _ _ h)

theorem t2_nP0a : D.tq 2 ∉ D.P0a.support :=
  not_mem_take_end D.p0_path _ (D.tq_ne (by decide))
theorem t0_nP0b : D.tq 0 ∉ D.P0b.support :=
  not_mem_drop_start D.p0_path _ (D.tq_ne (by decide))
theorem d2_nP3a : D.dq 2 ∉ D.P3a.support :=
  not_mem_take_end D.p3_path _ (D.dq_ne (by decide))
theorem d0_nP3b : D.dq 0 ∉ D.P3b.support :=
  not_mem_drop_start D.p3_path _ (D.dq_ne (by decide))
theorem d0_nQ0a : D.dq 0 ∉ D.Q0a.support := not_mem_take_end (D.qpath 0) _ D.a_ne_d0
theorem t0_nQ0b : D.tq 0 ∉ D.Q0b.support := not_mem_drop_start (D.qpath 0) _ D.a_ne_t0
theorem d2_nQ2a : D.dq 2 ∉ D.Q2a.support := not_mem_take_end (D.qpath 2) _ D.b_ne_d2
theorem t2_nQ2b : D.tq 2 ∉ D.Q2b.support := not_mem_drop_start (D.qpath 2) _ D.b_ne_t2

end MD
end Pieces
/-! ### Final assembly for an abstract rerouting option -/

def Allowed (P : Fin 4 → G.Subgraph) (Q : Fin 3 → G.Subgraph) (v : V) : Prop :=
  v ∈ (P 0).verts ∨ v ∈ (P 2).verts ∨ v ∈ (P 3).verts ∨ v ∈ (Q 0).verts ∨ v ∈ (Q 2).verts

structure Opt {P : Fin 4 → G.Subgraph} {Q : Fin 3 → G.Subgraph} (D : MD P Q)
    (ps : List (Fin 6 × Fin 6)) where
  x : Fin 3 → V
  y : Fin 3 → V
  w : ∀ k, G.Walk (x k) (y k)
  path : ∀ k, (w k).IsPath
  ne : ∀ k, x k ≠ y k
  disj : ∀ k k', k ≠ k' → ∀ v, v ∈ (w k).support → v ∉ (w k').support
  allowed : ∀ k v, v ∈ (w k).support → Allowed P Q v
  leafok : ∀ k v, v ∈ (w k).support → Lf D v → v = x k ∨ v = y k
  cover : ∀ i : Fin 6, ∃ k, lv D i = x k ∨ lv D i = y k
  edges : ∀ k a b, (w k).toSubgraph.Adj a b → (Msh P Q).Adj a b
  pairs : ∀ i j, pairAdj ps i j = true →
    ∃ k, (lv D i = x k ∧ lv D j = y k) ∨ (lv D i = y k ∧ lv D j = x k)
  ends : ∀ k, (∃ i, x k = lv D i) ∧ (∃ i, y k = lv D i)

section Final
variable [Fintype V] {P : Fin 4 → G.Subgraph} {Q : Fin 3 → G.Subgraph} (D : MD P Q)
  {u : V} (C : G.Walk u u) (hC : C.IsCycle) (hCM : C.toSubgraph ⊓ Msh P Q = ⨆ j, Q j)

theorem allowed_M {v : V} (h : Allowed P Q v) : v ∈ (Msh P Q).verts := by
  simp only [Msh, Subgraph.verts_sup, Subgraph.verts_iSup, Set.mem_union, Set.mem_iUnion]
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨0, h⟩
  · exact Or.inl ⟨2, h⟩
  · exact Or.inl ⟨3, h⟩
  · exact Or.inr ⟨0, h⟩
  · exact Or.inr ⟨2, h⟩

include D in
theorem allowed_avoid {v : V} (h : Allowed P Q v) (hq : v ∈ (Q 1).verts) : v ∉ (P 1).verts := by
  rcases h with h | h | h | h | h
  · exact D.notP (by decide) h
  · exact D.notP (by decide) h
  · exact D.notP (by decide) h
  · exact absurd hq (D.notQ (by decide) h)
  · exact absurd hq (D.notQ (by decide) h)

include hC hCM in
theorem final_of_opt {ps : List (Fin 6 × Fin 6)} (o : Opt D ps) (hconn : conn (labO D C) ps = true) :
    ∃ (u' : V) (C' : G.Walk u' u'), C'.IsCycle ∧
      (∀ v, v ∈ C'.support ↔ (((Og C Q).neighborSet v).Nonempty ∨ ∃ k, v ∈ (o.w k).support)) := by
  let N := Og C Q ⊔ pieces o.w
  have hcyc : N.IsCycles := by
    refine assembly (Og C Q) (Lf D) (fun v hv => O_leaf D C hC hCM hv)
      (fun v hv => O_other D C hC hCM hv) o.x o.y o.w o.path o.ne o.disj ?_ ?_ ?_ ?_
    · intro k
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := o.ends k
      exact ⟨hi ▸ Lf_lv D i, hj ▸ Lf_lv D j⟩
    · intro k v hv hx hy
      by_contra hne
      have hl := M_leaf D C hC hCM (allowed_M (o.allowed k v hv)) (Set.nonempty_iff_ne_empty.2 hne)
      rcases o.leafok k v hv hl with h | h
      · exact hx h
      · exact hy h
    · intro v hv
      obtain ⟨i, rfl⟩ := (Lf_iff D).1 hv
      exact o.cover i
    · intro k a b hab hO
      exact O_not_M C hCM hO (o.edges k a b hab)
  have hpiece_reach : ∀ k, N.Reachable (o.x k) (o.y k) := by
    intro k
    have := (o.w k).toSubgraph_connected.preconnected ⟨o.x k, (o.w k).start_mem_verts_toSubgraph⟩
      ⟨o.y k, (o.w k).end_mem_verts_toSubgraph⟩
    obtain ⟨q⟩ := this
    let f : (o.w k).toSubgraph.coe →g N := ⟨Subtype.val, fun h => Or.inr ((pieces_adj o.w _ _).2 ⟨k, h⟩)⟩
    exact ⟨q.map f⟩
  have hleaves : ∀ j, N.Reachable (lv D 0) (lv D j) := by
    refine conn_reach N (lv D) (labO D C) ps ?_ ?_ hconn
    · intro i j h
      exact ((labO_iff D C i j).1 h).mono le_sup_left
    · intro i j h
      obtain ⟨k, ⟨hi, hj⟩ | ⟨hi, hj⟩⟩ := o.pairs i j h
      · rw [hi, hj]; exact hpiece_reach k
      · rw [hi, hj]; exact (hpiece_reach k).symm
  have hreach := assembly_connected (Og C Q) (Lf D) o.x o.y o.w
    (fun k => ⟨(o.ends k).1.elim fun i hi => hi ▸ Lf_lv D i, (o.ends k).2.elim fun i hi => hi ▸ Lf_lv D i⟩)
    (lv D 0) (fun v hv => O_root D C hC hCM hv)
    (fun l hl => by obtain ⟨i, rfl⟩ := (Lf_iff D).1 hl; exact hleaves i)
  have hNG : N ≤ G := by
    intro a b h
    rcases h with h | h
    · simp only [Og, Cg, sdiff_adj, Subgraph.spanningCoe_adj] at h
      exact h.1.adj_sub
    · rw [pieces_adj] at h
      obtain ⟨k, hk⟩ := h
      exact hk.adj_sub
  have hr : (N.neighborSet (lv D 0)).Nonempty := by
    have h1 := O_leaf D C hC hCM (Lf_lv D 0)
    obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero (s := (Og C Q).neighborSet (lv D 0)) (by omega)
    exact ⟨z, Or.inl hz⟩
  obtain ⟨C', hC', hsupp⟩ := extract_cycle N hNG hcyc (lv D 0) hr hreach
  refine ⟨lv D 0, C', hC', fun v => ?_⟩
  rw [hsupp]
  show ((Og C Q ⊔ pieces o.w).neighborSet v).Nonempty ↔ _
  rw [neighborSet_sup]
  constructor
  · rintro ⟨z, hz | hz⟩
    · exact Or.inl ⟨z, hz⟩
    · rw [mem_neighborSet, pieces_adj] at hz
      obtain ⟨k, hk⟩ := hz
      exact Or.inr ⟨k, Walk.mem_support_of_adj_toSubgraph hk⟩
  · rintro (⟨z, hz⟩ | ⟨k, hk⟩)
    · exact ⟨z, Or.inl hz⟩
    · by_cases hx : v = o.x k
      · subst hx
        exact ⟨(o.w k).snd, Or.inr ((pieces_adj o.w _ _).2 ⟨k, (o.w k).toSubgraph_adj_snd
          (Walk.not_nil_of_ne (o.ne k))⟩)⟩
      · have hne : ((o.w k).toSubgraph.spanningCoe.neighborSet v).Nonempty := by
          by_cases hy : v = o.y k
          · subst hy; rw [piece_nbrs_end _ (o.path k) (o.ne k)]; exact Set.singleton_nonempty _
          · apply Set.nonempty_of_ncard_ne_zero
            rw [piece_nbrs_internal _ (o.path k) hk hx hy]; omega
        obtain ⟨z, hz⟩ := hne
        exact ⟨z, Or.inr ((pieces_adj o.w _ _).2 ⟨k, hz⟩)⟩

include hC hCM in
theorem not_M_O {v : V} (hv : v ∉ (Msh P Q).verts) :
    ((Og C Q).neighborSet v).Nonempty ↔ v ∈ C.support := by
  have hq : ∀ j, v ∉ (Q j).verts := fun j h => hv (by
    simp only [Msh, Subgraph.verts_sup, Subgraph.verts_iSup]; exact Or.inr (Set.mem_iUnion.2 ⟨j, h⟩))
  rw [Og_nbrs, Qg_nbrs_none hq, Set.sdiff_empty]
  constructor
  · intro h; by_contra hc; rw [Cg_empty C hc] at h; exact Set.not_nonempty_empty h
  · intro h
    apply Set.nonempty_of_ncard_ne_zero
    rw [Cg_card C hC h]; omega

include hCM in
theorem conclude (T : Set V) (hCT : IsRCycle G T C) (hT : Disjoint (Msh P Q).verts T)
    {ps : List (Fin 6 × Fin 6)} (o : Opt D ps) (hconn : conn (labO D C) ps = true) :
    ∃ (u' : V) (C' : G.Walk u' u'), IsRCycle G T C' ∧
      (∀ x ∈ C'.support, x ∈ (Q 1).verts → x ∉ (P 1).verts) ∧
      ∀ x, x ∉ (Msh P Q).verts → (x ∈ C'.support ↔ x ∈ C.support) := by
  obtain ⟨u', C', hC', hsupp⟩ := final_of_opt D C hCT.1 hCM o hconn
  have hpM : ∀ x, x ∉ (Msh P Q).verts → ∀ k, x ∉ (o.w k).support :=
    fun x hx k hk => hx (allowed_M (o.allowed k x hk))
  refine ⟨u', C', ⟨hC', fun v hv => ?_⟩, ?_, ?_⟩
  · have hvM : v ∉ (Msh P Q).verts := fun h => Set.disjoint_left.1 hT h hv
    rw [hsupp]; left
    exact (not_M_O C hCT.1 hCM hvM).2 (hCT.2 v hv)
  · intro x hx hq
    rcases (hsupp x).1 hx with h | ⟨k, hk⟩
    · have hl := M_leaf D C hCT.1 hCM (by
        simp only [Msh, Subgraph.verts_sup, Subgraph.verts_iSup]
        exact Or.inr (Set.mem_iUnion.2 ⟨1, hq⟩)) h
      obtain ⟨j, rfl | rfl⟩ := hl
      · exact D.notP (by decide) (D.tq_mem j)
      · exact D.notP (by decide) (D.dq_mem j)
    · exact allowed_avoid D (o.allowed k x hk) hq
  · intro x hx
    rw [hsupp, ← not_M_O C hCT.1 hCM hx]
    constructor
    · rintro (h | ⟨k, hk⟩)
      · exact h
      · exact absurd hk (hpM x hx k)
    · intro h; exact Or.inl h

end Final
/-! ### The three concrete options -/

section Options
variable [Fintype V] {P : Fin 4 → G.Subgraph} {Q : Fin 3 → G.Subgraph} (D : MD P Q)

theorem adj_of_edges_sub {x y x' y' a b : V} {w' : G.Walk x y} {w : G.Walk x' y'}
    (h : w'.edges ⊆ w.edges) (hab : w'.toSubgraph.Adj a b) : w.toSubgraph.Adj a b := by
  rw [Walk.adj_toSubgraph_iff_mem_edges] at hab ⊢; exact h hab

namespace MD
theorem M_of_P (i : Fin 4) {a b : V} (h : (D.pw i).toSubgraph.Adj a b) : (Msh P Q).Adj a b := by
  rw [D.psub] at h
  simp only [Msh, Subgraph.sup_adj, Subgraph.iSup_adj]; exact Or.inl ⟨i, h⟩
theorem M_of_Q (j : Fin 3) {a b : V} (h : (D.qw j).toSubgraph.Adj a b) : (Msh P Q).Adj a b := by
  rw [D.qsub] at h
  simp only [Msh, Subgraph.sup_adj, Subgraph.iSup_adj]; exact Or.inr ⟨j, h⟩

theorem P0a_e {a b : V} (h : D.P0a.toSubgraph.Adj a b) : (Msh P Q).Adj a b :=
  D.M_of_P 0 (adj_of_edges_sub (by
    intro e he; have := Walk.edges_takeUntil_subset_edges _ _ he; simpa [p0] using this) h)
theorem P0b_e {a b : V} (h : D.P0b.toSubgraph.Adj a b) : (Msh P Q).Adj a b :=
  D.M_of_P 0 (adj_of_edges_sub (by
    intro e he; have := Walk.edges_dropUntil_subset_edges _ _ he; simpa [p0] using this) h)
theorem P3a_e {a b : V} (h : D.P3a.toSubgraph.Adj a b) : (Msh P Q).Adj a b :=
  D.M_of_P 3 (adj_of_edges_sub (by
    intro e he; have := Walk.edges_takeUntil_subset_edges _ _ he; simpa [p3] using this) h)
theorem P3b_e {a b : V} (h : D.P3b.toSubgraph.Adj a b) : (Msh P Q).Adj a b :=
  D.M_of_P 3 (adj_of_edges_sub (by
    intro e he; have := Walk.edges_dropUntil_subset_edges _ _ he; simpa [p3] using this) h)
theorem Q0a_e {a b : V} (h : D.Q0a.toSubgraph.Adj a b) : (Msh P Q).Adj a b :=
  D.M_of_Q 0 (adj_of_edges_sub (Walk.edges_takeUntil_subset_edges _ _) h)
theorem Q0b_e {a b : V} (h : D.Q0b.toSubgraph.Adj a b) : (Msh P Q).Adj a b :=
  D.M_of_Q 0 (adj_of_edges_sub (Walk.edges_dropUntil_subset_edges _ _) h)
theorem Q2a_e {a b : V} (h : D.Q2a.toSubgraph.Adj a b) : (Msh P Q).Adj a b :=
  D.M_of_Q 2 (adj_of_edges_sub (Walk.edges_takeUntil_subset_edges _ _) h)
theorem Q2b_e {a b : V} (h : D.Q2b.toSubgraph.Adj a b) : (Msh P Q).Adj a b :=
  D.M_of_Q 2 (adj_of_edges_sub (Walk.edges_dropUntil_subset_edges _ _) h)

theorem leaf_P0 {v : V} (hl : Lf D v) (h : v ∈ (P 0).verts) :
    v = D.tq 0 ∨ v = D.tq 1 ∨ v = D.tq 2 := by
  obtain ⟨j, rfl | rfl⟩ := hl
  · fin_cases j <;> simp
  · exact absurd (D.dq_mem j) (D.notP (by decide) h)
theorem leaf_P3 {v : V} (hl : Lf D v) (h : v ∈ (P 3).verts) :
    v = D.dq 0 ∨ v = D.dq 1 ∨ v = D.dq 2 := by
  obtain ⟨j, rfl | rfl⟩ := hl
  · exact absurd (D.tq_mem j) (D.notP (by decide) h)
  · fin_cases j <;> simp
theorem leaf_Q {v : V} {c : Fin 3} (hl : Lf D v) (h : v ∈ (Q c).verts) : v = D.tq c ∨ v = D.dq c := by
  obtain ⟨j, rfl | rfl⟩ := hl
  · by_cases hj : j = c
    · subst hj; exact Or.inl rfl
    · exact absurd h (D.notQ hj (D.tq_memQ j))
  · by_cases hj : j = c
    · subst hj; exact Or.inr rfl
    · exact absurd h (D.notQ hj (D.dq_memQ j))
theorem leaf_P2 {v : V} (hl : Lf D v) : v ∉ (P 2).verts := by
  obtain ⟨j, rfl | rfl⟩ := hl
  · exact D.notP (by decide) (D.tq_mem j)
  · exact D.notP (by decide) (D.dq_mem j)

theorem P0b_path : D.P0b.IsPath := D.p0_path.dropUntil _
theorem P0a_path : D.P0a.IsPath := D.p0_path.takeUntil _
theorem P3b_path : D.P3b.IsPath := D.p3_path.dropUntil _
theorem P3a_path : D.P3a.IsPath := D.p3_path.takeUntil _
theorem Q0a_path : D.Q0a.IsPath := (D.qpath 0).takeUntil _
theorem Q0b_path : D.Q0b.IsPath := (D.qpath 0).dropUntil _
theorem Q2a_path : D.Q2a.IsPath := (D.qpath 2).takeUntil _
theorem Q2b_path : D.Q2b.IsPath := (D.qpath 2).dropUntil _
end MD

theorem pA_cases : ∀ i j : Fin 6, pairAdj pA i j = true →
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) ∨
    (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 3) := by decide
theorem pB_cases : ∀ i j : Fin 6, pairAdj pB i j = true →
    (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨ (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) ∨
    (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by decide
theorem pC_cases : ∀ i j : Fin 6, pairAdj pC i j = true →
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 4 ∧ j = 1) ∨ (i = 1 ∧ j = 4) ∨
    (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 3) := by decide

/-- Option A: `Q_0`, `P_0[t_1, t_2]`, `P_3[d_1, d_2]`. -/
noncomputable def optA : Opt D pA where
  x := ![D.tq 0, D.tq 1, D.dq 1]
  y := ![D.dq 0, D.tq 2, D.dq 2]
  w := fun k => match k with
    | 0 => D.qw 0
    | 1 => D.P0b
    | 2 => D.P3b
  path := by
    intro k; fin_cases k
    · exact D.qpath 0
    · exact D.P0b_path
    · exact D.P3b_path
  ne := by
    intro k; fin_cases k
    · exact tq_ne_dq D 0
    · exact D.tq_ne (by decide)
    · exact D.dq_ne (by decide)
  disj := by
    have h01 : ∀ v, v ∈ (D.qw 0).support → v ∉ D.P0b.support := fun v h1 h2 => by
      have := D.eq_tq (D.memQ.2 h1) (D.P0b_sub h2); subst this; exact D.t0_nP0b h2
    have h02 : ∀ v, v ∈ (D.qw 0).support → v ∉ D.P3b.support := fun v h1 h2 => by
      have := D.eq_dq (D.memQ.2 h1) (D.P3b_sub h2); subst this; exact D.d0_nP3b h2
    have h12 : ∀ v, v ∈ D.P0b.support → v ∉ D.P3b.support := fun v h1 h2 =>
      D.notP (by decide) (D.P0b_sub h1) (D.P3b_sub h2)
    intro k k' hk v h1 h2
    fin_cases k <;> fin_cases k' <;> simp at hk
    · exact h01 v h1 h2
    · exact h02 v h1 h2
    · exact h01 v h2 h1
    · exact h12 v h1 h2
    · exact h02 v h2 h1
    · exact h12 v h2 h1
  allowed := by
    intro k v hv; fin_cases k
    · exact Or.inr (Or.inr (Or.inr (Or.inl (D.memQ.2 hv))))
    · exact Or.inl (D.P0b_sub hv)
    · exact Or.inr (Or.inr (Or.inl (D.P3b_sub hv)))
  leafok := by
    intro k v hv hl; fin_cases k
    · exact D.leaf_Q hl (D.memQ.2 hv)
    · rcases D.leaf_P0 hl (D.P0b_sub hv) with rfl | rfl | rfl
      · exact absurd hv D.t0_nP0b
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases D.leaf_P3 hl (D.P3b_sub hv) with rfl | rfl | rfl
      · exact absurd hv D.d0_nP3b
      · exact Or.inl rfl
      · exact Or.inr rfl
  cover := by
    intro i; fin_cases i
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨2, Or.inl rfl⟩
    · exact ⟨1, Or.inr rfl⟩
    · exact ⟨2, Or.inr rfl⟩
  edges := by
    intro k a b h; fin_cases k
    · exact D.M_of_Q 0 h
    · exact D.P0b_e h
    · exact D.P3b_e h
  pairs := by
    intro i j h
    rcases pA_cases i j h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨1, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, rfl⟩⟩
  ends := by
    intro k; fin_cases k
    · exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
    · exact ⟨⟨2, rfl⟩, ⟨4, rfl⟩⟩
    · exact ⟨⟨3, rfl⟩, ⟨5, rfl⟩⟩

namespace MD
/-- `Q_0[t_0, a] ++ P_2 ++ Q_2[b, d_2]` -/
noncomputable def B0 : G.Walk (D.tq 0) (D.dq 2) := (D.Q0a.append (D.pw 2)).append D.Q2b
/-- `Q_2[t_2, b] ++ P_2⁻¹ ++ Q_0[a, d_0]` -/
noncomputable def C1 : G.Walk (D.tq 2) (D.dq 0) := (D.Q2a.append (D.pw 2).reverse).append D.Q0b

theorem B0_supp {v : V} (h : v ∈ D.B0.support) :
    v ∈ D.Q0a.support ∨ v ∈ (D.pw 2).support ∨ v ∈ D.Q2b.support := by
  simp only [B0, Walk.mem_support_append_iff] at h; tauto
theorem C1_supp {v : V} (h : v ∈ D.C1.support) :
    v ∈ D.Q2a.support ∨ v ∈ (D.pw 2).support ∨ v ∈ D.Q0b.support := by
  simp only [C1, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at h; tauto

theorem B0_path : D.B0.IsPath := by
  refine isPath_append_of (isPath_append_of D.Q0a_path (D.ppath 2) ?_) D.Q2b_path ?_
  · intro x h1 h2; exact D.eq_sp (D.memP.2 h2) (D.Q0a_sub h1)
  · intro x h1 h2
    rw [Walk.mem_support_append_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd (D.Q2b_sub h2) (D.notQ (by decide) (D.Q0a_sub h1))
    · exact D.eq_ep (D.memP.2 h1) (D.Q2b_sub h2)
theorem C1_path : D.C1.IsPath := by
  refine isPath_append_of (isPath_append_of D.Q2a_path (D.ppath 2).reverse ?_) D.Q0b_path ?_
  · intro x h1 h2
    rw [Walk.support_reverse, List.mem_reverse] at h2
    exact D.eq_ep (D.memP.2 h2) (D.Q2a_sub h1)
  · intro x h1 h2
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at h1
    rcases h1 with h1 | h1
    · exact absurd (D.Q0b_sub h2) (D.notQ (by decide) (D.Q2a_sub h1))
    · exact D.eq_sp (D.memP.2 h1) (D.Q0b_sub h2)

theorem B0_e {a b : V} (h : D.B0.toSubgraph.Adj a b) : (Msh P Q).Adj a b := by
  simp only [B0, Walk.toSubgraph_append, Subgraph.sup_adj] at h
  rcases h with (h | h) | h
  · exact D.Q0a_e h
  · exact D.M_of_P 2 h
  · exact D.Q2b_e h
theorem C1_e {a b : V} (h : D.C1.toSubgraph.Adj a b) : (Msh P Q).Adj a b := by
  simp only [C1, Walk.toSubgraph_append, Walk.toSubgraph_reverse, Subgraph.sup_adj] at h
  rcases h with (h | h) | h
  · exact D.Q2a_e h
  · exact D.M_of_P 2 h
  · exact D.Q0b_e h
end MD

/-- Option B: `Q_0[t_0,a] ++ P_2 ++ Q_2[b,d_2]`, `P_0[t_1, t_2]`, `P_3[d_0, d_1]`. -/
noncomputable def optB : Opt D pB where
  x := ![D.tq 0, D.tq 1, D.dq 0]
  y := ![D.dq 2, D.tq 2, D.dq 1]
  w := fun k => match k with
    | 0 => D.B0
    | 1 => D.P0b
    | 2 => D.P3a
  path := by
    intro k; fin_cases k
    · exact D.B0_path
    · exact D.P0b_path
    · exact D.P3a_path
  ne := by
    intro k; fin_cases k
    · intro h
      have h' : D.tq 0 = D.dq 2 := h
      exact D.notP (i := 0) (i' := 3) (by decide) (D.tq_mem 0) (h' ▸ D.dq_mem 2)
    · exact D.tq_ne (by decide)
    · exact D.dq_ne (by decide)
  disj := by
    have h01 : ∀ v, v ∈ D.B0.support → v ∉ D.P0b.support := fun v h1 h2 => by
      have hP0 := D.P0b_sub h2
      rcases D.B0_supp h1 with h | h | h
      · have := D.eq_tq (D.Q0a_sub h) hP0; subst this; exact D.t0_nP0b h2
      · exact D.notP (by decide) (D.memP.2 h) hP0
      · have := D.eq_tq (D.Q2b_sub h) hP0; subst this; exact D.t2_nQ2b h
    have h02 : ∀ v, v ∈ D.B0.support → v ∉ D.P3a.support := fun v h1 h2 => by
      have hP3 := D.P3a_sub h2
      rcases D.B0_supp h1 with h | h | h
      · have := D.eq_dq (D.Q0a_sub h) hP3; subst this; exact D.d0_nQ0a h
      · exact D.notP (by decide) (D.memP.2 h) hP3
      · have := D.eq_dq (D.Q2b_sub h) hP3; subst this; exact D.d2_nP3a h2
    have h12 : ∀ v, v ∈ D.P0b.support → v ∉ D.P3a.support := fun v h1 h2 =>
      D.notP (by decide) (D.P0b_sub h1) (D.P3a_sub h2)
    intro k k' hk v h1 h2
    fin_cases k <;> fin_cases k' <;> simp at hk
    · exact h01 v h1 h2
    · exact h02 v h1 h2
    · exact h01 v h2 h1
    · exact h12 v h1 h2
    · exact h02 v h2 h1
    · exact h12 v h2 h1
  allowed := by
    intro k v hv; fin_cases k
    · rcases D.B0_supp hv with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl (D.Q0a_sub h))))
      · exact Or.inr (Or.inl (D.memP.2 h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (D.Q2b_sub h))))
    · exact Or.inl (D.P0b_sub hv)
    · exact Or.inr (Or.inr (Or.inl (D.P3a_sub hv)))
  leafok := by
    intro k v hv hl; fin_cases k
    · rcases D.B0_supp hv with h | h | h
      · rcases D.leaf_Q hl (D.Q0a_sub h) with rfl | rfl
        · exact Or.inl rfl
        · exact absurd h D.d0_nQ0a
      · exact absurd (D.memP.2 h) (D.leaf_P2 hl)
      · rcases D.leaf_Q hl (D.Q2b_sub h) with rfl | rfl
        · exact absurd h D.t2_nQ2b
        · exact Or.inr rfl
    · rcases D.leaf_P0 hl (D.P0b_sub hv) with rfl | rfl | rfl
      · exact absurd hv D.t0_nP0b
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases D.leaf_P3 hl (D.P3a_sub hv) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hv D.d2_nP3a
  cover := by
    intro i; fin_cases i
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨2, Or.inl rfl⟩
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨2, Or.inr rfl⟩
    · exact ⟨1, Or.inr rfl⟩
    · exact ⟨0, Or.inr rfl⟩
  edges := by
    intro k a b h; fin_cases k
    · exact D.B0_e h
    · exact D.P0b_e h
    · exact D.P3a_e h
  pairs := by
    intro i j h
    rcases pB_cases i j h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨1, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, rfl⟩⟩
  ends := by
    intro k; fin_cases k
    · exact ⟨⟨0, rfl⟩, ⟨5, rfl⟩⟩
    · exact ⟨⟨2, rfl⟩, ⟨4, rfl⟩⟩
    · exact ⟨⟨1, rfl⟩, ⟨3, rfl⟩⟩

/-- Option C: `P_0[t_0, t_1]`, `Q_2[t_2,b] ++ P_2⁻¹ ++ Q_0[a,d_0]`, `P_3[d_1, d_2]`. -/
noncomputable def optC : Opt D pC where
  x := ![D.tq 0, D.tq 2, D.dq 1]
  y := ![D.tq 1, D.dq 0, D.dq 2]
  w := fun k => match k with
    | 0 => D.P0a
    | 1 => D.C1
    | 2 => D.P3b
  path := by
    intro k; fin_cases k
    · exact D.P0a_path
    · exact D.C1_path
    · exact D.P3b_path
  ne := by
    intro k; fin_cases k
    · exact D.tq_ne (by decide)
    · intro h
      have h' : D.tq 2 = D.dq 0 := h
      exact D.notP (i := 0) (i' := 3) (by decide) (D.tq_mem 2) (h' ▸ D.dq_mem 0)
    · exact D.dq_ne (by decide)
  disj := by
    have h01 : ∀ v, v ∈ D.P0a.support → v ∉ D.C1.support := fun v h1 h2 => by
      have hP0 := D.P0a_sub h1
      rcases D.C1_supp h2 with h | h | h
      · have := D.eq_tq (D.Q2a_sub h) hP0; subst this; exact D.t2_nP0a h1
      · exact D.notP (by decide) (D.memP.2 h) hP0
      · have := D.eq_tq (D.Q0b_sub h) hP0; subst this; exact D.t0_nQ0b h
    have h12 : ∀ v, v ∈ D.C1.support → v ∉ D.P3b.support := fun v h1 h2 => by
      have hP3 := D.P3b_sub h2
      rcases D.C1_supp h1 with h | h | h
      · have := D.eq_dq (D.Q2a_sub h) hP3; subst this; exact D.d2_nQ2a h
      · exact D.notP (by decide) (D.memP.2 h) hP3
      · have := D.eq_dq (D.Q0b_sub h) hP3; subst this; exact D.d0_nP3b h2
    have h02 : ∀ v, v ∈ D.P0a.support → v ∉ D.P3b.support := fun v h1 h2 =>
      D.notP (by decide) (D.P0a_sub h1) (D.P3b_sub h2)
    intro k k' hk v h1 h2
    fin_cases k <;> fin_cases k' <;> simp at hk
    · exact h01 v h1 h2
    · exact h02 v h1 h2
    · exact h01 v h2 h1
    · exact h12 v h1 h2
    · exact h02 v h2 h1
    · exact h12 v h2 h1
  allowed := by
    intro k v hv; fin_cases k
    · exact Or.inl (D.P0a_sub hv)
    · rcases D.C1_supp hv with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (D.Q2a_sub h))))
      · exact Or.inr (Or.inl (D.memP.2 h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (D.Q0b_sub h))))
    · exact Or.inr (Or.inr (Or.inl (D.P3b_sub hv)))
  leafok := by
    intro k v hv hl; fin_cases k
    · rcases D.leaf_P0 hl (D.P0a_sub hv) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hv D.t2_nP0a
    · rcases D.C1_supp hv with h | h | h
      · rcases D.leaf_Q hl (D.Q2a_sub h) with rfl | rfl
        · exact Or.inl rfl
        · exact absurd h D.d2_nQ2a
      · exact absurd (D.memP.2 h) (D.leaf_P2 hl)
      · rcases D.leaf_Q hl (D.Q0b_sub h) with rfl | rfl
        · exact absurd h D.t0_nQ0b
        · exact Or.inr rfl
    · rcases D.leaf_P3 hl (D.P3b_sub hv) with rfl | rfl | rfl
      · exact absurd hv D.d0_nP3b
      · exact Or.inl rfl
      · exact Or.inr rfl
  cover := by
    intro i; fin_cases i
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨1, Or.inr rfl⟩
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨2, Or.inl rfl⟩
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨2, Or.inr rfl⟩
  edges := by
    intro k a b h; fin_cases k
    · exact D.P0a_e h
    · exact D.C1_e h
    · exact D.P3b_e h
  pairs := by
    intro i j h
    rcases pC_cases i j h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨1, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, rfl⟩⟩
  ends := by
    intro k; fin_cases k
    · exact ⟨⟨0, rfl⟩, ⟨2, rfl⟩⟩
    · exact ⟨⟨4, rfl⟩, ⟨1, rfl⟩⟩
    · exact ⟨⟨3, rfl⟩, ⟨5, rfl⟩⟩

end Options
end TermCycDich.L310

open TermCycDich TermCycDich.L310 in
theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (T : Set V) {u : V}
    (C : G.Walk u u) (hC : IsRCycle G T C) (P : Fin 4 → G.Subgraph) (Q : Fin 3 → G.Subgraph)
    (hM : IsMesh (n := 2) (m := 1) P Q)
    (hCM : C.toSubgraph ⊓ ((⨆ i, P i) ⊔ (⨆ j, Q j)) = ⨆ j, Q j)
    (hT : Disjoint ((⨆ i, P i) ⊔ (⨆ j, Q j)).verts T) :
    ∃ (u' : V) (C' : G.Walk u' u'), IsRCycle G T C' ∧
      (∀ x ∈ C'.support, x ∈ (Q 1).verts → x ∉ (P 1).verts) ∧
      ∀ x, x ∉ ((⨆ i, P i) ⊔ (⨆ j, Q j)).verts → (x ∈ C'.support ↔ x ∈ C.support) := by
  obtain ⟨D⟩ := md_of_mesh hM
  have hCM' : C.toSubgraph ⊓ Msh P Q = ⨆ j, Q j := hCM
  have hns := labO_noSing D C hC.1 hCM'
  have hq := labO_connQ D C hC.1 hCM'
  have h3 := six_points' (labO D C) (labO_zero D C) (labO_le D C) hns hq
  simp only [Bool.or_eq_true] at h3
  rcases h3 with (h | h) | h
  · exact conclude D C hCM' T hC hT (optA D) h
  · exact conclude D C hCM' T hC hT (optB D) h
  · exact conclude D C hCM' T hC hT (optC D) h
