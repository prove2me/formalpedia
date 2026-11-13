-- Prove2me | solution 1 for RepellingPairs.claim_9_flow_dominance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:07:21.134216+00:00
-- url     : https://prove2.me/submissions/689f7b4e-678d-46fc-a4e0-cf559386c6db

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_IntegralFlow
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Theorems.Thm_RepellingPairs_walks_meet_of_cyclicallyOrdered
universe u v

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Claim9

open RepellingPairs RepellingPairs.Multigraph


section Walks

variable {V : Type u} {E : Type v} {G : Multigraph V E}

theorem support_append : ∀ {x y z : V} (p : G.Walk x y) (q : G.Walk y z),
    (p.append q).support = p.support ++ q.support.tail
  | _, _, _, .nil _, q => by cases q <;> rfl
  | _, _, _, .cons e h p, q => by
      simp only [Walk.append, Walk.support, support_append p q, List.cons_append]

theorem support_eq_cons {x y : V} (w : G.Walk x y) : w.support = x :: w.support.tail := by
  cases w <;> rfl

theorem start_mem {x y : V} (w : G.Walk x y) : x ∈ w.support := by
  rw [support_eq_cons]; exact List.mem_cons_self

theorem end_mem : ∀ {x y : V} (w : G.Walk x y), y ∈ w.support
  | _, _, .nil _ => List.mem_cons_self
  | _, _, .cons _ _ p => List.mem_cons_of_mem _ (end_mem p)

theorem mem_support_append {x y z : V} (p : G.Walk x y) (q : G.Walk y z) (a : V) :
    a ∈ (p.append q).support ↔ a ∈ p.support ∨ a ∈ q.support := by
  rw [support_append]
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_tail h)
  · rintro (h | h)
    · exact List.mem_append_left _ h
    · rw [support_eq_cons q] at h
      rcases List.mem_cons.1 h with h | h
      · subst h; exact List.mem_append_left _ (end_mem p)
      · exact List.mem_append_right _ h

theorem support_dropLast : ∀ {x y : V} (w : G.Walk x y), w.support = w.support.dropLast ++ [y]
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ p => by
      have ih := support_dropLast p
      have hne : p.support ≠ [] := by rw [support_eq_cons]; simp
      simp only [Walk.support]
      rw [List.dropLast_cons_of_ne_nil hne, List.cons_append, ← ih]

theorem support_append' {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).support = p.support.dropLast ++ q.support := by
  rw [support_append, support_dropLast p, List.append_assoc, List.singleton_append,
    ← support_eq_cons, List.dropLast_concat]

theorem edges_append : ∀ {x y z : V} (p : G.Walk x y) (q : G.Walk y z),
    (p.append q).edges = p.edges ++ q.edges
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons e h p, q => by
      simp only [Walk.append, Walk.edges, edges_append p q, List.cons_append]

theorem edges_reverse : ∀ {x y : V} (w : G.Walk x y), w.reverse.edges = w.edges.reverse
  | _, _, .nil _ => rfl
  | _, _, .cons e h p => by
      simp only [Walk.reverse, edges_append, edges_reverse p, Walk.edges, List.reverse_cons]

theorem mem_support_reverse : ∀ {x y : V} (w : G.Walk x y) (a : V),
    a ∈ w.reverse.support ↔ a ∈ w.support
  | _, _, .nil _, _ => Iff.rfl
  | _, _, .cons e h p, a => by
      simp only [Walk.reverse]
      rw [mem_support_append, mem_support_reverse p]
      simp only [Walk.support, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h | h)
        · exact Or.inr h
        · subst h; exact Or.inr (start_mem p)
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h

theorem suffix : ∀ {x y : V} (w : G.Walk x y) (z : V), z ∈ w.support →
    ∃ w' : G.Walk z y, ∀ a ∈ w'.support, a ∈ w.support
  | _, _, .nil _, z, hz => by
      simp only [Walk.support, List.mem_singleton] at hz
      subst hz; exact ⟨.nil _, fun a ha => ha⟩
  | _, _, .cons e h p, z, hz => by
      simp only [Walk.support, List.mem_cons] at hz
      rcases hz with hz | hz
      · subst hz; exact ⟨.cons e h p, fun a ha => ha⟩
      · obtain ⟨w', hw'⟩ := suffix p z hz
        exact ⟨w', fun a ha => List.mem_cons_of_mem _ (hw' a ha)⟩

/-- A contiguous block `R` of a duplicate-free list that contains an element before `m` and an
element after `m` contains `m`. -/
theorem contig {L X T S1 R S2 : List V} {m a b : V} (hL : L.Nodup) (h1 : L = X ++ m :: T)
    (h2 : L = S1 ++ R ++ S2) (ha : a ∈ X) (haR : a ∈ R) (hb : b ∈ T) (hbR : b ∈ R) : m ∈ R := by
  have nd : ∀ {P Q : List V} {x : V}, L = P ++ Q → x ∈ P → x ∈ Q → False :=
    fun hPQ hx hy => List.disjoint_of_nodup_append (hPQ ▸ hL) hx hy
  have h2' := h2
  rw [h1, List.append_assoc, List.append_eq_append_iff] at h2'
  rcases h2' with ⟨a', hS1, -⟩ | ⟨c', -, hc⟩
  · exact (nd (P := X) (Q := a' ++ R ++ S2) (x := a) (by rw [h2, hS1]; simp) ha (by simp [haR])).elim
  · rw [List.append_eq_append_iff] at hc
    rcases hc with ⟨a'', -, hS2⟩ | ⟨c'', hR, hmT⟩
    · exact (nd (P := S1 ++ R) (Q := a'' ++ m :: T) (x := b) (by rw [h2, hS2]) (by simp [hbR])
        (by simp [hb])).elim
    · rcases c'' with _ | ⟨h, rest⟩
      · simp only [List.nil_append, List.append_nil] at hmT hR
        exact (nd (P := S1 ++ R) (Q := S2) (x := b) (by rw [h2]) (by simp [hbR])
          (by rw [← hmT]; simp [hb])).elim
      · simp only [List.cons_append, List.cons.injEq] at hmT
        rw [hR, hmT.1]; simp

end Walks

end RepellingPairs.Dev.Claim9
end

section
set_option autoImplicit false
namespace RepellingPairs.Dev.Claim9
open RepellingPairs

def Par {k : ℕ} (a b c d : Fin k) : Prop :=
  CyclicallyOrdered a b d c ∨ CyclicallyOrdered b a d c ∨ CyclicallyOrdered a b c d ∨
    CyclicallyOrdered b a c d

/-- Position of `a` in the boundary order starting just after `i`. -/
def rk {k : ℕ} (i a : Fin k) : ℕ := if i.val < a.val then a.val - i.val - 1 else a.val + k - i.val - 1

theorem co_of_rk {k : ℕ} (i a b c d : Fin k) (h1 : rk i a < rk i b) (h2 : rk i b < rk i c)
    (h3 : rk i c < rk i d) : CyclicallyOrdered a b c d := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt; have hi := i.isLt
  unfold rk at h1 h2 h3
  unfold CyclicallyOrdered
  simp only [Fin.lt_def]
  split_ifs at h1 h2 h3 <;> omega

theorem co_rot {k : ℕ} {a b c d : Fin k} (h : CyclicallyOrdered a b c d) :
    CyclicallyOrdered b c d a := by
  unfold CyclicallyOrdered at *; tauto

theorem rk_lt {k : ℕ} (i j a b : Fin k) (ha : Config.onSide i j a = true)
    (hb : Config.onSide i j b = false) : rk i a < rk i b := by
  have := a.isLt; have := b.isLt; have := i.isLt; have := j.isLt
  unfold Config.onSide at ha hb
  unfold rk
  simp only [Fin.lt_def, Fin.le_def] at *
  split_ifs at ha hb ⊢ <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ha hb <;> omega

theorem rk_ne {k : ℕ} (i a b : Fin k) (h : a ≠ b) : rk i a ≠ rk i b := by
  have := a.isLt; have := b.isLt; have := i.isLt
  rw [Fin.ne_iff_vne] at h
  unfold rk
  split_ifs <;> omega

theorem comb2 {k : ℕ} (i j l1 l2 r1 r2 : Fin k) (h1 : Config.onSide i j l1 = true)
    (h2 : Config.onSide i j l2 = true) (h3 : Config.onSide i j r1 = false)
    (h4 : Config.onSide i j r2 = false) (hl : l1 ≠ l2) (hr : r1 ≠ r2) : Par l1 l2 r1 r2 := by
  have a1 := rk_lt i j _ _ h1 h3; have a2 := rk_lt i j _ _ h1 h4
  have a3 := rk_lt i j _ _ h2 h3; have a4 := rk_lt i j _ _ h2 h4
  have hl' := rk_ne i _ _ hl; have hr' := rk_ne i _ _ hr
  unfold Par
  rcases Nat.lt_or_gt_of_ne hl' with x | x <;> rcases Nat.lt_or_gt_of_ne hr' with y | y
  · exact Or.inr (Or.inr (Or.inl (co_of_rk i _ _ _ _ x a3 y)))
  · exact Or.inl (co_of_rk i _ _ _ _ x a4 y)
  · exact Or.inr (Or.inr (Or.inr (co_of_rk i _ _ _ _ x a1 y)))
  · exact Or.inr (Or.inl (co_of_rk i _ _ _ _ x a2 y))

theorem comb1 {k : ℕ} (i j l1 l2 l r t : Fin k) (h1 : Config.onSide i j l1 = true)
    (h2 : Config.onSide i j l2 = true) (h0 : Config.onSide i j l = true)
    (h3 : Config.onSide i j r = false)
    (h4 : Config.onSide i j t = false) (hl : l1 ≠ l2) (ha : l ≠ l1) (hb : l ≠ l2) :
    CyclicallyOrdered l1 l l2 t ∨ CyclicallyOrdered l l1 t l2 ∨ Par l1 l2 l r := by
  have := rk_lt i j _ _ h1 h3; have := rk_lt i j _ _ h1 h4
  have := rk_lt i j _ _ h2 h3; have := rk_lt i j _ _ h2 h4
  have := rk_lt i j _ _ h0 h3; have := rk_lt i j _ _ h0 h4
  have hl' := rk_ne i _ _ hl; have ha' := rk_ne i _ _ ha; have hb' := rk_ne i _ _ hb
  unfold Par
  rcases Nat.lt_or_gt_of_ne hl' with x | x <;> rcases Nat.lt_or_gt_of_ne ha' with y | y <;>
    rcases Nat.lt_or_gt_of_ne hb' with z | z
  all_goals first
    | omega
    | exact Or.inl (co_of_rk i l1 l l2 t (by omega) (by omega) (by omega))
    | exact Or.inr (Or.inl (co_rot (co_of_rk i l2 l l1 t (by omega) (by omega) (by omega))))
    | exact Or.inr (Or.inr (Or.inl (co_rot (co_of_rk i l l1 l2 r (by omega) (by omega) (by omega)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl
        (co_rot (co_of_rk i l l2 l1 r (by omega) (by omega) (by omega))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (co_of_rk i l1 l2 l r (by omega) (by omega) (by omega))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (co_of_rk i l2 l1 l r (by omega) (by omega) (by omega))))))

end RepellingPairs.Dev.Claim9
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Claim9

open RepellingPairs RepellingPairs.Multigraph


section Count

variable {V : Type u} {E : Type v} (χ : V → Bool)

/-- `1` if the two ends of the edge have different colours. -/
def bval (G : Multigraph V E) (e : E) : ℕ :=
  Sym2.lift ⟨fun a b => if χ a = χ b then 0 else 1, fun a b => by simp [eq_comm]⟩ (G.ends e)

/-- Number of colour changes along a walk. -/
def cnt {G : Multigraph V E} {x y : V} (w : G.Walk x y) : ℕ := (w.edges.map (bval χ G)).sum

variable {G : Multigraph V E}

theorem cnt_cons {x v y : V} (e : E) (h : G.ends e = s(x, v)) (p : G.Walk v y) :
    cnt χ (.cons e h p) = (if χ x = χ v then 0 else 1) + cnt χ p := by
  simp [cnt, Walk.edges, bval, h]

theorem le_cnt : ∀ {x y : V} (w : G.Walk x y), (if χ x = χ y then 0 else 1) ≤ cnt χ w
  | _, _, .nil _ => by simp
  | x, y, .cons (v := v) e h p => by
      have ih := le_cnt p
      rw [cnt_cons]
      generalize χ x = cx at *
      generalize χ v = cv at *
      generalize χ y = cy at *
      cases cx <;> cases cv <;> cases cy <;> simp at * <;> omega

theorem cnt_const : ∀ {x y : V} (w : G.Walk x y) (c : Bool), (∀ z ∈ w.support, χ z = c) →
    cnt χ w = 0
  | _, _, .nil _, _, _ => rfl
  | x, y, .cons (v := v) e h p, c, hc => by
      rw [cnt_cons, cnt_const p c (fun z hz => hc z (List.mem_cons_of_mem _ hz)),
        hc x List.mem_cons_self, hc v (List.mem_cons_of_mem _ (start_mem p))]
      simp

/-- Along the walk the colour never goes back from `true` to `false`. -/
def Mono {x y : V} (w : G.Walk x y) : Prop :=
  ∀ (m : V) (w1 : G.Walk x m) (w2 : G.Walk m y), w = w1.append w2 → χ m = true →
    ∀ z ∈ w2.support, χ z = true

theorem mono_bound : ∀ {x y : V} (w : G.Walk x y), Mono χ w →
    cnt χ w + (χ x).toNat + (!χ y).toNat ≤ 1
  | x, _, .nil _, _ => by cases χ x <;> simp [cnt, Walk.edges]
  | x, y, .cons (v := v) e h p, hm => by
      cases hx : χ x
      · have hp : Mono χ p := fun m w1 w2 hw hm' =>
          hm m (.cons e h w1) w2 (by rw [hw]; rfl) hm'
        have ih := mono_bound p hp
        rw [cnt_cons, hx]
        cases hv : χ v <;> simp [hv] at ih ⊢ <;> omega
      · have hall := hm x (.nil x) (.cons e h p) rfl hx
        rw [cnt_const χ _ true hall, hall y (end_mem _)]
        simp

theorem cnt_reverse {x y : V} (w : G.Walk x y) : cnt χ w.reverse = cnt χ w := by
  unfold cnt; rw [edges_reverse, List.map_reverse, List.sum_reverse]

theorem list_sum_count [Fintype E] [DecidableEq E] (l : List E) (f : E → ℕ) :
    (l.map f).sum = ∑ e, l.count e * f e := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.count_cons, ih, add_mul,
        Finset.sum_add_distrib, beq_iff_eq]
      simp [add_comm]

theorem cnt_eq_sum [Fintype E] [DecidableEq E] {x y : V} (w : G.Walk x y) :
    cnt χ w = ∑ e, w.edges.count e * bval χ G e := list_sum_count _ _

end Count

theorem sum_swap {α : Type*} {β : Type*} [Fintype β] (s : Multiset α) (g : α → β → ℕ) :
    (s.map fun a => ∑ x, g a x).sum = ∑ x, (s.map fun a => g a x).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.map_cons, Multiset.sum_cons, ih, Finset.sum_add_distrib]

section OS

variable {V : Type u} {E : Type v} {k : ℕ} (χ : V → Bool) (G : OSInstance V E k) (i j : Fin k)

/-- `1` if the terminal's vertex has the wrong colour for its side (`false` = side `onSide`). -/
def mis (t : Fin k) : ℕ := if χ (G.term t) = !Config.onSide i j t then 0 else 1

theorem cross_le (a b : Fin k) (w : G.graph.Walk (G.term a) (G.term b)) :
    Config.chordCross i j s(a, b) ≤ cnt χ w + mis χ G i j a + mis χ G i j b := by
  have h := le_cnt χ w
  simp only [Config.chordCross, Sym2.lift_mk, mis]
  generalize χ (G.term a) = ca at *
  generalize χ (G.term b) = cb at *
  generalize Config.onSide i j a = oa
  generalize Config.onSide i j b = ob
  cases ca <;> cases cb <;> cases oa <;> cases ob <;> simp at * <;> omega

/-- Weight of a chord: the miscolouring of its two ends. -/
def Mc (c : Sym2 (Fin k)) : ℕ := ∑ t, mis χ G i j t * Config.chordDeg t c

theorem Mc_mk (a b : Fin k) : Mc χ G i j s(a, b) = mis χ G i j a + mis χ G i j b := by
  simp [Mc, Config.chordDeg, Sym2.lift_mk, mul_add, Finset.sum_add_distrib]

theorem sum_mis_deg (C : Config k) :
    ∑ t, mis χ G i j t * Config.deg C t = (C.map (Mc χ G i j)).sum := by
  unfold Mc Config.deg
  rw [sum_swap]
  congr 1; ext t
  rw [Multiset.sum_map_mul_left]

variable [Fintype E] [DecidableEq E]

theorem dist_le_of_colouring (P : PathStructure G) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F')
    (hF : ∀ p ∈ F, cnt χ (P.path p.1 p.2).1 + mis χ G i j p.1 + mis χ G i j p.2 ≤
      Config.chordCross i j s(p.1, p.2)) :
    Config.dist (PathFlow.chords F') i j ≤ Config.dist (DesignatedFlow.chords F) i j := by
  have e1 : Config.dist (PathFlow.chords F') i j ≤
      (F'.map fun q => cnt χ q.path.1).sum + (F'.map fun q => Mc χ G i j s(q.src, q.tgt)).sum := by
    rw [← Multiset.sum_map_add]
    unfold Config.dist PathFlow.chords
    rw [Multiset.map_map]
    refine Multiset.sum_map_le_sum_map _ _ fun q _ => ?_
    simp only [Function.comp, Mc_mk]
    have := cross_le χ G i j q.src q.tgt q.path.1
    omega
  have e2 : (F'.map fun q => cnt χ q.path.1).sum ≤
      (F.map fun p => cnt χ (P.path p.1 p.2).1).sum := by
    simp only [cnt_eq_sum, sum_swap, Multiset.sum_map_mul_right]
    exact Finset.sum_le_sum fun e _ => Nat.mul_le_mul_right _ (h2 e)
  have e3 : (F'.map fun q => Mc χ G i j s(q.src, q.tgt)).sum =
      (F.map fun p => Mc χ G i j s(p.1, p.2)).sum := by
    have a := sum_mis_deg χ G i j (PathFlow.chords F')
    have b := sum_mis_deg χ G i j (DesignatedFlow.chords F)
    simp only [PathFlow.chords, DesignatedFlow.chords, Multiset.map_map, Function.comp] at a b
    rw [← a, ← b]
    exact Finset.sum_congr rfl fun t _ => by
      have := h4 t
      simp only [PathFlow.chords, DesignatedFlow.chords] at this
      rw [this]
  have e4 : (F.map fun p => cnt χ (P.path p.1 p.2).1).sum +
      (F.map fun p => Mc χ G i j s(p.1, p.2)).sum ≤ Config.dist (DesignatedFlow.chords F) i j := by
    rw [← Multiset.sum_map_add]
    unfold Config.dist DesignatedFlow.chords
    rw [Multiset.map_map]
    refine Multiset.sum_map_le_sum_map _ _ fun p hp => ?_
    simp only [Function.comp, Mc_mk]
    have := hF p hp
    omega
  omega

end OS

end RepellingPairs.Dev.Claim9
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Claim9

open RepellingPairs RepellingPairs.Multigraph


section B

variable {V : Type u} {E : Type v} {k : ℕ} {G : OSInstance V E k} (P : PathStructure G)

theorem mem_path_symm (a b : Fin k) (z : V) :
    z ∈ (P.path b a).1.support ↔ z ∈ (P.path a b).1.support := by
  rw [P.path_symm]; exact mem_support_reverse _ _

theorem chord_mem {F : DesignatedFlow k} {p : Fin k × Fin k} (hp : p ∈ F) :
    s(p.1, p.2) ∈ DesignatedFlow.chords F :=
  Multiset.mem_map_of_mem _ hp

theorem disj_of_par {F : DesignatedFlow k} (h5 : Property5 P F) {a b c d : Fin k}
    (hab : s(a, b) ∈ DesignatedFlow.chords F) (hcd : s(c, d) ∈ DesignatedFlow.chords F)
    (hp : Par a b c d) (z : V) (hz1 : z ∈ (P.path a b).1.support)
    (hz2 : z ∈ (P.path c d).1.support) : False := by
  have hba : s(b, a) ∈ DesignatedFlow.chords F := Sym2.eq_swap ▸ hab
  have hdc : s(d, c) ∈ DesignatedFlow.chords F := Sym2.eq_swap ▸ hcd
  have hz1' := (mem_path_symm P a b z).2 hz1
  have hz2' := (mem_path_symm P c d z).2 hz2
  rcases hp with h | h | h | h
  · exact h5 a b d c h hab hcd z hz1 hz2
  · exact h5 b a d c h hba hcd z hz1' hz2
  · exact h5 a b c d h hab hdc z hz1 hz2'
  · exact h5 b a c d h hba hdc z hz1' hz2'

variable (F : DesignatedFlow k) (i j : Fin k)

/-- `z` lies on the designated path of a unit of `F` with both ends on the side `onSide`. -/
def InU (z : V) : Prop :=
  ∃ p ∈ F, Config.onSide i j p.1 = true ∧ Config.onSide i j p.2 = true ∧
    z ∈ (P.path p.1 p.2).1.support

/-- `z` reaches a terminal off the side `onSide` by a walk avoiding every such path. -/
def Good (z : V) : Prop :=
  ∃ t, Config.onSide i j t = false ∧ ∃ q : G.graph.Walk z (G.term t), ∀ y ∈ q.support, ¬ InU P F i j y

variable {P F i j}

theorem disj_AA_BB (h5 : Property5 P F) (hF : NoTrivialPair F) {p p' : Fin k × Fin k}
    (hp : p ∈ F) (hp' : p' ∈ F) (A1 : Config.onSide i j p.1 = true)
    (A2 : Config.onSide i j p.2 = true) (B1 : Config.onSide i j p'.1 = false)
    (B2 : Config.onSide i j p'.2 = false) (z : V) (hz : z ∈ (P.path p.1 p.2).1.support)
    (hz' : z ∈ (P.path p'.1 p'.2).1.support) : False :=
  disj_of_par P h5 (chord_mem hp) (chord_mem hp')
    (comb2 i j _ _ _ _ A1 A2 B1 B2 (hF p hp) (hF p' hp')) z hz hz'

theorem good_of_BB (h5 : Property5 P F) (hF : NoTrivialPair F) {p : Fin k × Fin k} (hp : p ∈ F)
    (B1 : Config.onSide i j p.1 = false) (B2 : Config.onSide i j p.2 = false) (z : V)
    (hz : z ∈ (P.path p.1 p.2).1.support) : Good P F i j z := by
  obtain ⟨w', hw'⟩ := suffix _ z hz
  exact ⟨p.2, B2, w', fun y hy ⟨p', hp', A1, A2, hy'⟩ =>
    disj_AA_BB h5 hF hp' hp A1 A2 B1 B2 y hy' (hw' y hy)⟩

theorem not_U_of_good {z : V} (h : Good P F i j z) : ¬ InU P F i j z := by
  obtain ⟨t, -, q, hq⟩ := h
  exact hq z (start_mem q)

/-- The core step: along a crossing unit path, oriented from its end on the side `onSide`, a good
vertex is followed only by good vertices. -/
theorem good_forward (h5 : Property5 P F) (hF : NoTrivialPair F) {l r : Fin k}
    (hl : Config.onSide i j l = true) (hr : Config.onSide i j r = false)
    (hch : s(l, r) ∈ DesignatedFlow.chords F) {m : V} (w1 : G.graph.Walk (G.term l) m)
    (w2 : G.graph.Walk m (G.term r)) (hw : (P.path l r).1 = w1.append w2)
    (hm : Good P F i j m) : ∀ z ∈ w2.support, Good P F i j z := by
  obtain ⟨t, ht, g, hg⟩ := hm
  have key : ∀ y ∈ w2.support, ¬ InU P F i j y := by
    rintro y hy ⟨p', hp', A1, A2, hyZ⟩
    have hmZ : m ∉ (P.path p'.1 p'.2).1.support := fun h =>
      hg m (start_mem g) ⟨p', hp', A1, A2, h⟩
    have hyQ : y ∈ (P.path l r).1.support := by
      rw [hw, mem_support_append]; exact Or.inr hy
    by_cases hz1 : ∃ z1 ∈ w1.support, z1 ∈ (P.path p'.1 p'.2).1.support
    · obtain ⟨z1, hz1w, hz1Z⟩ := hz1
      rcases P.meet l r p'.1 p'.2 with hd | ⟨x', y', R, hI, ⟨q1, q2, hsub⟩, -⟩
      · exact hd y hyQ hyZ
      · apply hmZ
        have hz1Q : z1 ∈ (P.path l r).1.support := by
          rw [hw, mem_support_append]; exact Or.inl hz1w
        have h1 : (P.path l r).1.support = w1.support.dropLast ++ m :: w2.support.tail := by
          rw [hw, support_append']; exact congrArg _ (support_eq_cons w2)
        have h2 : (P.path l r).1.support = q1.support.dropLast ++ R.support ++ q2.support.tail := by
          rw [hsub, support_append', support_append, List.append_assoc]
        rw [support_dropLast, List.mem_append, List.mem_singleton] at hz1w
        rw [support_eq_cons, List.mem_cons] at hy
        rcases hz1w with ha | ha
        · rcases hy with hb | hb
          · exact hb ▸ hyZ
          · exact ((hI.1 m).1 (contig (P.path l r).2 h1 h2 ha ((hI.1 z1).2 ⟨hz1Q, hz1Z⟩) hb
              ((hI.1 y).2 ⟨hyQ, hyZ⟩))).2
        · exact ha ▸ hz1Z
    · simp only [not_exists, not_and] at hz1
      have hne1 : l ≠ p'.1 := by
        rintro rfl; exact hz1 _ (start_mem _) (start_mem _)
      have hne2 : l ≠ p'.2 := by
        rintro rfl; exact hz1 _ (start_mem _) (end_mem _)
      have avoid : ∀ v ∈ (w1.append g).support, v ∉ (P.path p'.1 p'.2).1.support := by
        intro v hv hvZ
        rcases (mem_support_append _ _ _).1 hv with h | h
        · exact hz1 v h hvZ
        · exact hg v h ⟨p', hp', A1, A2, hvZ⟩
      rcases comb1 i j p'.1 p'.2 l r t A1 A2 hl hr ht (hF p' hp') hne1 hne2 with c | c | c
      · obtain ⟨v, hv1, hv2⟩ := walks_meet_of_cyclicallyOrdered G c (P.path p'.1 p'.2).1
          (w1.append g)
        exact avoid v hv2 hv1
      · obtain ⟨v, hv1, hv2⟩ := walks_meet_of_cyclicallyOrdered G c (w1.append g)
          (P.path p'.1 p'.2).1
        exact avoid v hv1 hv2
      · exact disj_of_par P h5 (chord_mem hp') hch c y hyZ hyQ
  intro z hz
  obtain ⟨w', hw'⟩ := suffix w2 z hz
  exact ⟨r, hr, w', fun y hy => key y (hw' y hy)⟩

variable (P F i j)

/-- The colouring: `true` exactly on good vertices. -/
noncomputable def chi (z : V) : Bool := by
  classical exact decide (Good P F i j z)

variable {P F i j}

theorem chi_iff (z : V) : chi P F i j z = true ↔ Good P F i j z := by
  unfold chi; simp

theorem mono_of_cross (h5 : Property5 P F) (hF : NoTrivialPair F) {l r : Fin k}
    (hl : Config.onSide i j l = true) (hr : Config.onSide i j r = false)
    (hch : s(l, r) ∈ DesignatedFlow.chords F) : Mono (chi P F i j) (P.path l r).1 :=
  fun _ w1 w2 hw hm z hz =>
    (chi_iff z).2 (good_forward h5 hF hl hr hch w1 w2 hw ((chi_iff _).1 hm) z hz)

variable [Fintype E] [DecidableEq E]

theorem unit_bound (h5 : Property5 P F) (hF : NoTrivialPair F) (p : Fin k × Fin k) (hp : p ∈ F) :
    cnt (chi P F i j) (P.path p.1 p.2).1 + mis (chi P F i j) G i j p.1 +
      mis (chi P F i j) G i j p.2 ≤ Config.chordCross i j s(p.1, p.2) := by
  cases h1 : Config.onSide i j p.1 <;> cases h2 : Config.onSide i j p.2
  · have hall : ∀ z ∈ (P.path p.1 p.2).1.support, chi P F i j z = true := fun z hz =>
      (chi_iff z).2 (good_of_BB h5 hF hp h1 h2 z hz)
    rw [cnt_const _ _ true hall]
    simp [mis, Config.chordCross, h1, h2, hall _ (start_mem _), hall _ (end_mem _)]
  · have hm := mono_of_cross h5 hF h2 h1 (Sym2.eq_swap ▸ chord_mem hp)
    have hb := mono_bound _ _ hm
    rw [P.path_symm p.2 p.1, cnt_reverse]
    simp only [mis, Config.chordCross, Sym2.lift_mk, h1, h2]
    revert hb
    cases chi P F i j (G.term p.1) <;> cases chi P F i j (G.term p.2) <;> simp
  · have hm := mono_of_cross h5 hF h1 h2 (chord_mem hp)
    have hb := mono_bound _ _ hm
    simp only [mis, Config.chordCross, Sym2.lift_mk, h1, h2]
    revert hb
    cases chi P F i j (G.term p.1) <;> cases chi P F i j (G.term p.2) <;> simp
  · have hall : ∀ z ∈ (P.path p.1 p.2).1.support, chi P F i j z = false := fun z hz => by
      rw [Bool.eq_false_iff, ne_eq, chi_iff]
      exact fun hg => not_U_of_good hg ⟨p, hp, h1, h2, hz⟩
    rw [cnt_const _ _ false hall]
    simp [mis, Config.chordCross, h1, h2, hall _ (start_mem _), hall _ (end_mem _)]

end B

end RepellingPairs.Dev.Claim9

namespace RepellingPairs


theorem chk_claim_9_flow_dominance {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F') (h5 : Property5 P F) (hF : NoTrivialPair F) :
    Config.Dominates (DesignatedFlow.chords F) (PathFlow.chords F') := by
  intro i j
  exact Dev.Claim9.dist_le_of_colouring _ G i j P F F' h2 h4
    (fun p hp => Dev.Claim9.unit_bound h5 hF p hp)

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_claim_9_flow_dominance := @RepellingPairs.chk_claim_9_flow_dominance
