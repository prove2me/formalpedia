-- Prove2me | solution 1 for TraceAdopt.LPReform.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:41:59.789523+00:00
-- url     : https://prove2.me/submissions/245949d1-ee11-4894-9a56-1142cc3aa7d5

import Definitions.Def_TraceAdopt_LPReform_BiLP10Graph
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_TraceAdopt_LPReform_proposition_3
import Theorems.Thm_TraceAdopt_LPReform_proposition_5
import Theorems.Thm_TraceAdopt_LPReform_proposition_7
import Theorems.Thm_TraceAdopt_LPReform_proposition_8

namespace TAChordal

open SimpleGraph

variable {V T : Type} [DecidableEq V] [DecidableEq T] {t : SimpleGraph T} (ht : t.IsTree) (X : T → Finset V)
include ht

theorem path_eq {x y : T} (p q : t.Walk x y) (hp : p.IsPath) (hq : q.IsPath) : p = q :=
  congrArg Subtype.val ((ht.isAcyclic.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)

/-- The unique path to the root. -/
noncomputable def P (r : T) (x : T) : t.Walk x r := (ht.connected.preconnected x r).some.bypass

theorem P_isPath (r x : T) : (P ht r x).IsPath := Walk.bypass_isPath _

theorem P_unique (r x : T) (p : t.Walk x r) (hp : p.IsPath) : p = P ht r x :=
  path_eq ht p _ hp (P_isPath ht r x)

variable (hiii : ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support →
    X s ∩ X s'' ⊆ X s')
include hiii

theorem convex {v : V} {a b : T} (ha : v ∈ X a) (hb : v ∈ X b) (p : t.Walk a b) (hp : p.IsPath) :
    ∀ c ∈ p.support, v ∈ X c :=
  fun c hc => hiii a c b p hp hc (Finset.mem_inter.2 ⟨ha, hb⟩)

/-- The `P`-minimal node of the subtree of `v` lies on the root path of every node of it. -/
theorem F (r : T) (v : V) (z y : T) (hz : v ∈ X z)
    (hmin : ∀ w, v ∈ X w → (P ht r z).length ≤ (P ht r w).length) (hy : v ∈ X y) :
    z ∈ (P ht r y).support := by
  classical
  obtain ⟨q0⟩ := ht.connected.preconnected y z
  set q := q0.bypass with hqdef
  have hq : q.IsPath := Walk.bypass_isPath _
  have hqN : ∀ c ∈ q.support, v ∈ X c := convex ht X hiii hy hz q hq
  by_cases hzr : z = r
  · subst hzr; exact Walk.end_mem_support _
  -- decompose the root path of `z`
  have hPz := P_isPath ht r z
  generalize hPdef : P ht r z = Pz at hPz hmin
  cases Pz with
  | nil => exact absurd rfl hzr
  | @cons _ z' _ hadj rest =>
    have hrest : rest.IsPath := hPz.of_cons
    have hzrest : z ∉ rest.support := ((Walk.cons_isPath_iff hadj rest).1 hPz).2
    have hPz' : P ht r z' = rest := (P_unique ht r z' rest hrest).symm
    -- the parent of `z` is outside the subtree of `v`
    have hz'N : v ∉ X z' := by
      intro h
      have := hmin z' h
      rw [hPz', Walk.length_cons] at this
      omega
    -- the root path of `z` meets the subtree of `v` only at `z`
    have honly : ∀ w ∈ rest.support, v ∉ X w := by
      intro w hw hvw
      have hpath : (Walk.cons hadj (rest.takeUntil w hw)).IsPath := by
        rw [Walk.cons_isPath_iff]
        exact ⟨hrest.takeUntil hw, fun h => hzrest (rest.support_takeUntil_subset_support hw h)⟩
      apply hz'N
      apply convex ht X hiii hz hvw _ hpath
      simp
    have happ : (q.append (Walk.cons hadj rest)).IsPath := by
      rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons,
        List.nodup_append]
      refine ⟨(Walk.isPath_def _).1 hq, (Walk.isPath_def _).1 hrest, ?_⟩
      intro a ha b hb hab
      subst hab
      exact honly a hb (hqN a ha)
    have := P_unique ht r y _ happ
    rw [← this]
    exact (Walk.mem_support_append_iff _ _).2 (Or.inl (Walk.end_mem_support _))

/-- Comparison of two nodes on a root path. -/
theorem order (r : T) (y z zu : T) (hz : z ∈ (P ht r y).support) (hzu : zu ∈ (P ht r y).support)
    (hlen : (P ht r zu).length ≤ (P ht r z).length) :
    z ∈ ((P ht r y).takeUntil zu hzu).support := by
  classical
  have hspec := Walk.take_spec (P ht r y) hzu
  have hdrop : (P ht r y).dropUntil zu hzu = P ht r zu :=
    P_unique ht r zu _ ((P_isPath ht r y).dropUntil hzu)
  have hz' : z ∈ (((P ht r y).takeUntil zu hzu).append ((P ht r y).dropUntil zu hzu)).support := by
    rw [hspec]; exact hz
  rcases (Walk.mem_support_append_iff _ _).1 hz' with h | h
  · exact h
  · rw [hdrop] at h
    have hspec2 := Walk.take_spec (P ht r zu) h
    have hdrop2 : (P ht r zu).dropUntil z h = P ht r z :=
      P_unique ht r z _ ((P_isPath ht r zu).dropUntil h)
    have hl : (P ht r zu).length = ((P ht r zu).takeUntil z h).length + (P ht r z).length := by
      conv_lhs => rw [← hspec2]
      rw [Walk.length_append, hdrop2]
    have h0 : ((P ht r zu).takeUntil z h).length = 0 := by omega
    have := Walk.eq_of_length_eq_zero h0
    subst this
    exact Walk.end_mem_support _

/-- Existence of a simplicial vertex relative to a finite set. -/
theorem simplicial [Fintype T] (U : Finset V) (hU : U.Nonempty) (hcov : ∀ v ∈ U, ∃ y, v ∈ X y) :
    ∃ v ∈ U, ∃ z, v ∈ X z ∧ ∀ u ∈ U, ∀ y, u ∈ X y → v ∈ X y → u ∈ X z := by
  classical
  have hne : Nonempty T := ht.connected.nonempty
  let r : T := Classical.arbitrary T
  have hzv : ∀ v ∈ U, ∃ z, v ∈ X z ∧ ∀ w, v ∈ X w → (P ht r z).length ≤ (P ht r w).length := by
    intro v hv
    obtain ⟨y0, hy0⟩ := hcov v hv
    obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun w => v ∈ X w))
      (fun w => (P ht r w).length) ⟨y0, by simp [hy0]⟩
    refine ⟨z, by simpa using hz, fun w hw => hmin w (by simp [hw])⟩
  choose! zv hzvX hzvmin using hzv
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image U (fun v => (P ht r (zv v)).length) hU
  refine ⟨v, hv, zv v, hzvX v hv, ?_⟩
  intro u hu y huy hvy
  have h1 := F ht X hiii r v (zv v) y (hzvX v hv) (hzvmin v hv) hvy
  have h2 := F ht X hiii r u (zv u) y (hzvX u hu) (hzvmin u hu) huy
  have h3 := order ht X hiii r y (zv v) (zv u) h1 h2 (hvmax u hu)
  exact hiii y (zv v) (zv u) _ ((P_isPath ht r y).takeUntil h2) h3
    (Finset.mem_inter.2 ⟨huy, hzvX u hu⟩)

/-- No nonempty set in which every vertex has an in-neighbour along a bag-pair. -/
theorem noBad [Fintype T] (ℓ : V → V → ℕ)
    (h1 : ∀ z, ∀ u ∈ X z, ∀ v ∈ X z, u ≠ v → ℓ u v + ℓ v u = 1)
    (h2 : ∀ z, ∀ u ∈ X z, ∀ v ∈ X z, ∀ x ∈ X z, u ≠ v → v ≠ x → u ≠ x →
      ℓ u v + ℓ v x + ℓ x u ≤ 2) :
    ∀ U : Finset V, U.Nonempty →
      (∀ v ∈ U, ∃ u ∈ U, u ≠ v ∧ (∃ y, u ∈ X y ∧ v ∈ X y) ∧ ℓ u v = 1) → False := by
  classical
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
  intro hU hin
  have hcov : ∀ v ∈ U, ∃ y, v ∈ X y := by
    intro v hv
    obtain ⟨u, _, _, ⟨y, _, hvy⟩, _⟩ := hin v hv
    exact ⟨y, hvy⟩
  obtain ⟨v, hv, z, hvz, hsimp⟩ := simplicial ht X hiii U hU hcov
  obtain ⟨u0, hu0, hu0v, ⟨y0, hu0y, hvy0⟩, hl0⟩ := hin v hv
  have hu0z : u0 ∈ X z := hsimp u0 hu0 y0 hu0y hvy0
  apply ih (U.erase v) (Finset.erase_ssubset hv) ⟨u0, Finset.mem_erase.2 ⟨hu0v, hu0⟩⟩
  intro w hw
  obtain ⟨hwv, hwU⟩ := Finset.mem_erase.1 hw
  obtain ⟨x, hx, hxw, ⟨y, hxy, hwy⟩, hlx⟩ := hin w hwU
  by_cases hxv : x = v
  · subst hxv
    have hwz : w ∈ X z := hsimp w hwU y hwy hxy
    have hu0w : u0 ≠ w := by
      intro h
      subst h
      have := h1 z u0 hu0z x hvz hu0v
      omega
    refine ⟨u0, Finset.mem_erase.2 ⟨hu0v, hu0⟩, hu0w, ⟨z, hu0z, hwz⟩, ?_⟩
    have hs := h1 z u0 hu0z w hwz hu0w
    have ht3 := h2 z u0 hu0z x hvz w hwz hu0v hxw hu0w
    omega
  · exact ⟨x, Finset.mem_erase.2 ⟨hxv, hx⟩, hxw, ⟨y, hxy, hwy⟩, hlx⟩

end TAChordal
namespace TAElim

open SimpleGraph

/-- An elimination structure of width `ω` extracted from a tree decomposition. -/
theorem elim_of_td {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ω : ℕ)
    (hG : RobertsonSeymour1986.GM5.TreewidthLE G ω) :
    ∃ (rk : V → ℕ) (C : V → Finset V) (π : V → V),
      Function.Injective rk ∧ (∀ v, v ∈ C v) ∧ (∀ v, ∀ u ∈ C v, rk v ≤ rk u) ∧
      (∀ v, (C v).card ≤ ω + 1) ∧
      (∀ v, ((C v).erase v).Nonempty → rk v < rk (π v) ∧ (C v).erase v ⊆ C (π v)) ∧
      (∀ K : Finset V, K.Nonempty → (∀ u ∈ K, ∀ w ∈ K, u ≠ w → G.Adj u w) →
        ∃ v, K ⊆ C v) := by
  classical
  obtain ⟨T, hT, t, X, ⟨htree, hcov, hedge, hpath⟩, hw⟩ := hG
  by_cases hn : IsEmpty V
  · refine ⟨fun _ => 0, fun _ => ∅, id, fun a => (hn.false a).elim, fun v => (hn.false v).elim,
      fun v => (hn.false v).elim, fun v => (hn.false v).elim, fun v => (hn.false v).elim, ?_⟩
    rintro K ⟨v, _⟩; exact (hn.false v).elim
  let n := Fintype.card V
  let idx : V → ℕ := fun v => (Fintype.equivFin V v).val
  have hidx : ∀ v, idx v < n := fun v => (Fintype.equivFin V v).isLt
  have hidxinj : Function.Injective idx := by
    intro a b h
    exact (Fintype.equivFin V).injective (Fin.ext h)
  haveI : Nonempty T := htree.connected.nonempty
  let r : T := Classical.arbitrary T
  let L : T → ℕ := fun y => (TAChordal.P htree r y).length
  have hz : ∀ v : V, ∃ z, v ∈ X z ∧ ∀ w, v ∈ X w → L z ≤ L w := by
    intro v
    obtain ⟨y0, hy0⟩ := hcov v
    obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun w => v ∈ X w)) L
      ⟨y0, by simp [hy0]⟩
    exact ⟨z, by simpa using hz, fun w hw => hmin w (by simp [hw])⟩
  choose zv hzvX hzvmin using hz
  let d : V → ℕ := fun v => L (zv v)
  let Bd : ℕ := Finset.univ.sup d + 1
  have hdB : ∀ v, d v < Bd := fun v => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  let rk : V → ℕ := fun v => idx v + (Bd - d v) * n
  have hrkinj : Function.Injective rk := by
    intro a b hab
    have h1 : rk a % n = idx a := by
      simp only [rk]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hidx a)]
    have h2 : rk b % n = idx b := by
      simp only [rk]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hidx b)]
    apply hidxinj
    rw [← h1, ← h2, hab]
  have hrkd : ∀ v u, rk v < rk u → d u ≤ d v := by
    intro v u h
    by_contra hcon
    push Not at hcon
    have h1 : Bd - d u + 1 ≤ Bd - d v := by have := hdB u; omega
    have h2 : (Bd - d u + 1) * n ≤ (Bd - d v) * n := Nat.mul_le_mul_right n h1
    have h3 : rk u < (Bd - d u + 1) * n := by
      simp only [rk]; rw [Nat.add_mul, Nat.one_mul]; have := hidx u; omega
    have h4 : (Bd - d v) * n ≤ rk v := by simp only [rk]; omega
    omega
  let C : V → Finset V := fun v => insert v ((X (zv v)).filter (fun u => rk v < rk u))
  have hCsub : ∀ v, C v ⊆ X (zv v) := by
    intro v u hu
    simp only [C, Finset.mem_insert, Finset.mem_filter] at hu
    rcases hu with rfl | ⟨hu, _⟩
    · exact hzvX u
    · exact hu
  -- the key comparison
  have key : ∀ (y : T) (v u : V), v ∈ X y → u ∈ X y → d u ≤ d v → u ∈ X (zv v) := by
    intro y v u hvy huy hle
    have h1 := TAChordal.F htree X hpath r v (zv v) y (hzvX v) (hzvmin v) hvy
    have h2 := TAChordal.F htree X hpath r u (zv u) y (hzvX u) (hzvmin u) huy
    have h3 := TAChordal.order htree X hpath r y (zv v) (zv u) h1 h2 hle
    exact hpath y (zv v) (zv u) _ ((TAChordal.P_isPath htree r y).takeUntil h2) h3
      (Finset.mem_inter.2 ⟨huy, hzvX u⟩)
  let π : V → V := fun v =>
    if h : ((C v).erase v).Nonempty then
      Classical.choose (Finset.exists_min_image ((C v).erase v) rk h) else v
  refine ⟨rk, C, π, hrkinj, fun v => Finset.mem_insert_self _ _, ?_, ?_, ?_, ?_⟩
  · intro v u hu
    simp only [C, Finset.mem_insert, Finset.mem_filter] at hu
    rcases hu with rfl | ⟨_, h⟩
    · exact le_rfl
    · exact h.le
  · intro v
    exact le_trans (Finset.card_le_card (hCsub v)) (hw _)
  · intro v hS
    have hspec := Classical.choose_spec (Finset.exists_min_image ((C v).erase v) rk hS)
    have hπv : π v = Classical.choose (Finset.exists_min_image ((C v).erase v) rk hS) := by
      simp only [π, dif_pos hS]
    rw [hπv]
    set w := Classical.choose (Finset.exists_min_image ((C v).erase v) rk hS)
    obtain ⟨hwS, hwmin⟩ := hspec
    have hwC : w ∈ C v := Finset.mem_of_mem_erase hwS
    have hwv : w ≠ v := Finset.ne_of_mem_erase hwS
    have hrvw : rk v < rk w := by
      simp only [C, Finset.mem_insert, Finset.mem_filter] at hwC
      rcases hwC with h | ⟨_, h⟩
      · exact absurd h hwv
      · exact h
    refine ⟨hrvw, ?_⟩
    intro u hu
    have huC : u ∈ C v := Finset.mem_of_mem_erase hu
    have huv : u ≠ v := Finset.ne_of_mem_erase hu
    by_cases huw : u = w
    · rw [huw]; exact Finset.mem_insert_self _ _
    have hlt : rk w < rk u := lt_of_le_of_ne (hwmin u hu) (fun h => huw (hrkinj h).symm)
    have huX : u ∈ X (zv v) := hCsub v huC
    have hwX : w ∈ X (zv v) := hCsub v hwC
    have := key (zv v) w u hwX huX (hrkd w u hlt)
    simp only [C, Finset.mem_insert, Finset.mem_filter]
    exact Or.inr ⟨this, hlt⟩
  · intro K hK hclq
    obtain ⟨v, hvK, hvmin⟩ := Finset.exists_min_image K rk hK
    refine ⟨v, fun u hu => ?_⟩
    by_cases huv : u = v
    · rw [huv]; exact Finset.mem_insert_self _ _
    have hlt : rk v < rk u := lt_of_le_of_ne (hvmin u hu) (fun h => huv (hrkinj h).symm)
    obtain ⟨y, hvy, huy⟩ := hedge v u (hclq v hvK u hu (Ne.symm huv))
    have := key y v u hvy huy (hrkd v u hlt)
    simp only [C, Finset.mem_insert, Finset.mem_filter]
    exact Or.inr ⟨this, hlt⟩

end TAElim
namespace TAPP

open SimpleGraph

/-- Sufficient condition for the path axiom (iii). -/
theorem iii_of_walks {V T : Type} [DecidableEq V] {t : SimpleGraph T} (ht : t.IsAcyclic)
    (X : T → Finset V)
    (h : ∀ v a b, v ∈ X a → v ∈ X b → ∃ w : t.Walk a b, ∀ c ∈ w.support, v ∈ X c) :
    ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s' := by
  classical
  intro s s' s'' p hp hs' v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨w, hw⟩ := h v s s'' hv.1 hv.2
  have heq : (⟨w.bypass, w.bypass_isPath⟩ : t.Path s s'') = ⟨p, hp⟩ :=
    (ht.subsingleton_path s s'').elim _ _
  have hq : w.bypass = p := congrArg Subtype.val heq
  apply hw
  apply w.support_bypass_subset_support
  rw [hq]; exact hs'

variable {Z : Type} [Fintype Z] [DecidableEq Z]

/-- The graph of a parent map. -/
def ppGraph (par : Z → Z) : SimpleGraph Z :=
  SimpleGraph.fromEdgeSet {e | ∃ z, e = s(z, par z)}

variable (rt : Z) (par : Z → Z) (μ : Z → ℕ) (hrt : par rt = rt)
  (hμ : ∀ z, z ≠ rt → μ (par z) < μ z)

include hμ in
theorem pp_ne (z : Z) (hz : z ≠ rt) : par z ≠ z := by
  intro h; have := hμ z hz; rw [h] at this; omega

include hμ in
theorem pp_adj (z : Z) (hz : z ≠ rt) : (ppGraph par).Adj z (par z) := by
  simp only [ppGraph, fromEdgeSet_adj, Set.mem_setOf_eq]
  exact ⟨⟨z, rfl⟩, (pp_ne rt par μ hμ z hz).symm⟩

include hrt hμ in
theorem pp_reach (z : Z) : ∃ k, par^[k] z = rt := by
  induction h : μ z using Nat.strong_induction_on generalizing z with
  | _ N ih =>
    by_cases hz : z = rt
    · exact ⟨0, hz⟩
    · obtain ⟨k, hk⟩ := ih (μ (par z)) (h ▸ hμ z hz) (par z) rfl
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

include hμ in
/-- A walk from `z` up to the root along parents. -/
theorem pp_walk_up (z : Z) : ∃ w : (ppGraph par).Walk z rt,
    ∀ c ∈ w.support, ∃ k, par^[k] z = c := by
  induction h : μ z using Nat.strong_induction_on generalizing z with
  | _ N ih =>
    by_cases hz : z = rt
    · subst hz; exact ⟨Walk.nil, fun c hc => ⟨0, by simp at hc; exact hc.symm⟩⟩
    · obtain ⟨w, hw⟩ := ih (μ (par z)) (h ▸ hμ z hz) (par z) rfl
      refine ⟨Walk.cons (pp_adj rt par μ hμ z hz) w, fun c hc => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨0, rfl⟩
      · obtain ⟨k, hk⟩ := hw c hc
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

include hrt hμ in
theorem pp_isTree : (ppGraph par).IsTree := by
  classical
  have hconn : (ppGraph par).Connected := by
    haveI : Nonempty Z := ⟨rt⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨wa, _⟩ := pp_walk_up rt par μ hμ a
    obtain ⟨wb, _⟩ := pp_walk_up rt par μ hμ b
    exact ⟨wa.append wb.reverse⟩
  rw [isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hE : (ppGraph par).edgeSet = (fun z => s(z, par z)) '' {z | z ≠ rt} := by
    ext e
    simp only [ppGraph, edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨z, rfl⟩, hd⟩
      refine ⟨z, ?_, rfl⟩
      intro hz; subst hz; apply hd; rw [hrt]; simp
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, rfl⟩, ?_⟩
      simp only [Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
      exact (pp_ne rt par μ hμ z hz).symm
  have hinj : Set.InjOn (fun z => s(z, par z)) {z | z ≠ rt} := by
    intro a ha b hb hab
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hab
    rcases hab with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      have e1 := hμ a ha
      have e2 := hμ b hb
      rw [h2] at e1
      rw [← h1] at e2
      omega
  rw [Nat.card_coe_set_eq, hE, Set.ncard_image_of_injOn hinj]
  have : {z : Z | z ≠ rt} = (({rt} : Set Z)ᶜ) := by ext; simp
  rw [this, Set.ncard_compl, Set.ncard_singleton]
  have : Nonempty Z := ⟨rt⟩
  have : 0 < Nat.card Z := Nat.card_pos
  omega

variable {V : Type} [DecidableEq V] (B : Z → Finset V) (top : V → Z)
  (htop : ∀ x, x ∈ B (top x))
  (hchain : ∀ x z, x ∈ B z → z ≠ top x → z ≠ rt ∧ x ∈ B (par z))

include hμ hchain in
theorem pp_walk_top (x : V) (z : Z) (hz : x ∈ B z) :
    ∃ w : (ppGraph par).Walk z (top x), ∀ c ∈ w.support, x ∈ B c := by
  induction h : μ z using Nat.strong_induction_on generalizing z with
  | _ N ih =>
    by_cases hzt : z = top x
    · subst hzt; exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hz⟩
    · obtain ⟨hzr, hpz⟩ := hchain x z hz hzt
      obtain ⟨w, hw⟩ := ih (μ (par z)) (h ▸ hμ z hzr) (par z) hpz rfl
      refine ⟨Walk.cons (pp_adj rt par μ hμ z hzr) w, fun c hc => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hz
      · exact hw c hc

include hrt hμ hchain in
theorem pp_iii : ∀ (s s' s'' : Z) (p : (ppGraph par).Walk s s''), p.IsPath → s' ∈ p.support →
    B s ∩ B s'' ⊆ B s' := by
  apply iii_of_walks (pp_isTree rt par μ hrt hμ).isAcyclic B
  intro x a b ha hb
  obtain ⟨wa, hwa⟩ := pp_walk_top rt par μ hμ B top hchain x a ha
  obtain ⟨wb, hwb⟩ := pp_walk_top rt par μ hμ B top hchain x b hb
  refine ⟨wa.append wb.reverse, fun c hc => ?_⟩
  rcases (Walk.mem_support_append_iff _ _).1 hc with hc | hc
  · exact hwa c hc
  · rw [Walk.support_reverse, List.mem_reverse] at hc
    exact hwb c hc

end TAPP

namespace TABin

open SimpleGraph TraceAdopt.LPReform

section
variable {V : Type} [Fintype V] [DecidableEq V] (rk : V → ℕ) (C : V → Finset V) (π : V → V)

/-- Node type of the binarised clique forest: original nodes, connectors, and a root. -/
abbrev Nd (V : Type) := V ⊕ V ⊕ Unit

noncomputable def idx (w : V) : ℕ := (Fintype.equivFin V w).val

theorem idx_inj : Function.Injective (idx (V := V)) := by
  intro a b h
  exact (Fintype.equivFin V).injective (Fin.ext h)

theorem idx_lt (w : V) : idx w < Fintype.card V := (Fintype.equivFin V w).isLt

def HasPar (w : V) : Prop := ((C w).erase w).Nonempty

open Classical in
noncomputable def Pn (w : V) : Nd V := if HasPar C w then Sum.inl (π w) else Sum.inr (Sum.inr ())

open Classical in
noncomputable def cand (w : V) : Finset V :=
  Finset.univ.filter (fun w' => Pn C π w' = Pn C π w ∧ idx w' < idx w)

open Classical in
noncomputable def prevOf (w : V) : V :=
  if h : (cand C π w).Nonempty then Classical.choose (Finset.exists_max_image (cand C π w) idx h)
  else w

theorem prevOf_spec (w : V) (h : (cand C π w).Nonempty) :
    prevOf C π w ∈ cand C π w ∧ ∀ w' ∈ cand C π w, idx w' ≤ idx (prevOf C π w) := by
  classical
  have := Classical.choose_spec (Finset.exists_max_image (cand C π w) idx h)
  simp only [prevOf, dif_pos h]
  convert this

open Classical in
noncomputable def par : Nd V → Nd V
  | Sum.inl w => Sum.inr (Sum.inl w)
  | Sum.inr (Sum.inl w) =>
      if (cand C π w).Nonempty then Sum.inr (Sum.inl (prevOf C π w)) else Pn C π w
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr ())

open Classical in
noncomputable def B : Nd V → Finset V
  | Sum.inl v => C v
  | Sum.inr (Sum.inl w) => if HasPar C w then C (π w) else ∅
  | Sum.inr (Sum.inr _) => ∅

open Classical in
noncomputable def rkP (Bd : ℕ) (w : V) : ℕ := if HasPar C w then rk (π w) else Bd

noncomputable def μ (Bd : ℕ) : Nd V → ℕ
  | Sum.inl w => (Bd - rk w) * (Fintype.card V + 2)
  | Sum.inr (Sum.inl w) => (Bd - rkP rk C π Bd w) * (Fintype.card V + 2) + idx w + 1
  | Sum.inr (Sum.inr _) => 0

theorem Pn_eq_inl {w u : V} (h : Pn C π w = Sum.inl u) : HasPar C w ∧ π w = u := by
  classical
  unfold Pn at h
  split_ifs at h with hw
  · exact ⟨hw, Sum.inl_injective h⟩

theorem Pn_eq_rt {w : V} (h : Pn C π w = Sum.inr (Sum.inr ())) : ¬ HasPar C w := by
  classical
  unfold Pn at h
  split_ifs at h with hw
  exact hw

theorem rkP_eq {Bd : ℕ} {w w' : V} (h : Pn C π w' = Pn C π w) :
    rkP rk C π Bd w' = rkP rk C π Bd w := by
  classical
  unfold rkP
  by_cases hw : HasPar C w
  · have e : Pn C π w = Sum.inl (π w) := by simp [Pn, hw]
    rw [e] at h
    obtain ⟨h1, h2⟩ := Pn_eq_inl C π h
    simp [hw, h1, h2]
  · have e : Pn C π w = Sum.inr (Sum.inr ()) := by simp [Pn, hw]
    rw [e] at h
    have h1 := Pn_eq_rt C π h
    simp [hw, h1]

variable (hCv : ∀ v, v ∈ C v) (hCr : ∀ v, ∀ u ∈ C v, rk v ≤ rk u)
  (hπ : ∀ v, ((C v).erase v).Nonempty → rk v < rk (π v) ∧ (C v).erase v ⊆ C (π v))

include hπ in
theorem μ_dec (Bd : ℕ) (hBd : ∀ v, rk v < Bd) (z : Nd V) (hz : z ≠ Sum.inr (Sum.inr ())) :
    μ rk C π Bd (par C π z) < μ rk C π Bd z := by
  classical
  have hK : ∀ w : V, idx w < Fintype.card V := idx_lt
  rcases z with w | w | u
  · -- original node
    simp only [par, μ]
    have hlt : rk w < rkP rk C π Bd w := by
      unfold rkP
      split_ifs with h
      · exact (hπ w h).1
      · exact hBd w
    have h1 : Bd - rkP rk C π Bd w + 1 ≤ Bd - rk w := by
      have : rkP rk C π Bd w ≤ Bd := by
        unfold rkP; split_ifs with h
        · exact (hBd _).le
        · exact le_rfl
      omega
    have h2 : (Bd - rkP rk C π Bd w + 1) * (Fintype.card V + 2) ≤
        (Bd - rk w) * (Fintype.card V + 2) := Nat.mul_le_mul_right _ h1
    have := hK w
    nlinarith
  · simp only [par]
    split_ifs with hc
    · obtain ⟨hmem, _⟩ := prevOf_spec C π w hc
      simp only [cand, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      simp only [μ]
      rw [rkP_eq rk C π hmem.1]
      omega
    · unfold Pn
      split_ifs with hp
      · simp only [μ, rkP, hp, if_true]
        omega
      · simp only [μ]
        omega
  · exact absurd (by cases u; rfl) hz

end


section Main
variable {V : Type} [Fintype V] [DecidableEq V] (rk : V → ℕ) (C : V → Finset V) (π : V → V)
  (hrk : Function.Injective rk)
  (hCv : ∀ v, v ∈ C v) (hCr : ∀ v, ∀ u ∈ C v, rk v ≤ rk u)
  (hπ : ∀ v, ((C v).erase v).Nonempty → rk v < rk (π v) ∧ (C v).erase v ⊆ C (π v))

include hπ in
theorem chain (x : V) (z : Nd V) (hx : x ∈ B C π z) (hzx : z ≠ Sum.inl x) :
    z ≠ Sum.inr (Sum.inr ()) ∧ x ∈ B C π (par C π z) := by
  classical
  rcases z with v | w | u
  · simp only [B] at hx
    have hvx : v ≠ x := fun h => hzx (by rw [h])
    have hxe : x ∈ (C v).erase v := Finset.mem_erase.2 ⟨Ne.symm hvx, hx⟩
    have hp : HasPar C v := ⟨x, hxe⟩
    refine ⟨by simp, ?_⟩
    simp only [par, B]
    rw [if_pos hp]
    exact (hπ v hp).2 hxe
  · simp only [B] at hx
    split_ifs at hx with hp
    · refine ⟨by simp, ?_⟩
      simp only [par]
      split_ifs with hc
      · obtain ⟨hmem, _⟩ := prevOf_spec C π w hc
        simp only [cand, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        have e : Pn C π w = Sum.inl (π w) := by simp [Pn, hp]
        rw [e] at hmem
        obtain ⟨h1, h2⟩ := Pn_eq_inl C π hmem.1
        simp only [B, h1, if_true, h2]
        exact hx
      · simp only [Pn, hp, if_true, B]
        exact hx
    · simp at hx
  · simp [B] at hx

theorem uniq_noPrev {w1 w2 : V} (h1 : ¬ (cand C π w1).Nonempty) (h2 : ¬ (cand C π w2).Nonempty)
    (hP : Pn C π w1 = Pn C π w2) : w1 = w2 := by
  classical
  by_contra hne
  have hi : idx w1 ≠ idx w2 := fun h => hne (idx_inj h)
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · exact h2 ⟨w1, by simp [cand, hP, h]⟩
  · exact h1 ⟨w2, by simp [cand, hP, h]⟩

theorem uniq_prev {w0 w1 w2 : V} (h1 : (cand C π w1).Nonempty) (h2 : (cand C π w2).Nonempty)
    (e1 : prevOf C π w1 = w0) (e2 : prevOf C π w2 = w0) : w1 = w2 := by
  classical
  obtain ⟨m1, max1⟩ := prevOf_spec C π w1 h1
  obtain ⟨m2, max2⟩ := prevOf_spec C π w2 h2
  rw [e1] at m1 max1
  rw [e2] at m2 max2
  simp only [cand, Finset.mem_filter, Finset.mem_univ, true_and] at m1 m2
  have hP : Pn C π w1 = Pn C π w2 := m1.1.symm.trans m2.1
  by_contra hne
  have hi : idx w1 ≠ idx w2 := fun h => hne (idx_inj h)
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · have := max2 w1 (by simp [cand, hP, h])
    omega
  · have := max1 w2 (by simp [cand, hP.symm, h])
    omega


theorem par_conn_eq (w : V) (z : Nd V) (h : par C π (Sum.inr (Sum.inl w)) = z) :
    ((cand C π w).Nonempty ∧ z = Sum.inr (Sum.inl (prevOf C π w))) ∨
      (¬ (cand C π w).Nonempty ∧ z = Pn C π w) := by
  classical
  simp only [par] at h
  split_ifs at h with hc
  · exact Or.inl ⟨hc, h.symm⟩
  · exact Or.inr ⟨hc, h.symm⟩

theorem Pn_ne_conn (w w0 : V) : Pn C π w ≠ Sum.inr (Sum.inl w0) := by
  classical
  unfold Pn; split_ifs <;> simp

include hrk hCv hCr hπ in
theorem binTD_props (Bd : ℕ) (hBd : ∀ v, rk v < Bd)
    (G : SimpleGraph V) (hclq : ∀ a b, G.Adj a b → ∃ v, a ∈ C v ∧ b ∈ C v) :
    RobertsonSeymour1986.GM5.IsTreeDecomposition G (TAPP.ppGraph (par C π)) (B C π) ∧
    par C π (Sum.inr (Sum.inr ())) = Sum.inr (Sum.inr ()) ∧
    (∀ z, z ≠ Sum.inr (Sum.inr ()) → (TAPP.ppGraph (par C π)).Adj z (par C π z)) ∧
    (∀ z, ∃ k : ℕ, (par C π)^[k] z = Sum.inr (Sum.inr ())) ∧
    (∀ z, (Finset.univ.filter (fun z' => z' ≠ Sum.inr (Sum.inr ()) ∧ par C π z' = z)).card ≤ 2) := by
  classical
  have hrt : par C π (Sum.inr (Sum.inr ())) = Sum.inr (Sum.inr ()) := by simp [par]
  have hμ := μ_dec rk C π hπ Bd hBd
  refine ⟨⟨TAPP.pp_isTree _ _ (μ rk C π Bd) hrt hμ, ?_, ?_, ?_⟩, hrt,
    fun z hz => TAPP.pp_adj _ _ (μ rk C π Bd) hμ z hz,
    fun z => TAPP.pp_reach _ _ (μ rk C π Bd) hrt hμ z, ?_⟩
  · intro x; exact ⟨Sum.inl x, hCv x⟩
  · intro a b hab
    obtain ⟨v, hv⟩ := hclq a b hab
    exact ⟨Sum.inl v, hv⟩
  · exact TAPP.pp_iii _ _ (μ rk C π Bd) hrt hμ (B C π) (fun x => Sum.inl x)
      (chain rk C π hπ)
  · intro z
    have hinl : ∀ (a : Nd V) (w : V), par C π a = Sum.inl w → ∃ w', a = Sum.inr (Sum.inl w') ∧
        ¬ (cand C π w').Nonempty ∧ Pn C π w' = Sum.inl w := by
      intro a w h
      rcases a with a | a | a
      · simp [par] at h
      · rcases par_conn_eq C π a _ h with ⟨_, h2⟩ | ⟨h1, h2⟩
        · simp at h2
        · exact ⟨a, rfl, h1, h2.symm⟩
      · simp [par] at h
    rcases z with u | w0 | r0
    · apply le_trans _ (by norm_num : 1 ≤ 2)
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨wa, rfl, ha1, ha2⟩ := hinl a u ha.2
      obtain ⟨wb, rfl, hb1, hb2⟩ := hinl b u hb.2
      rw [uniq_noPrev C π ha1 hb1 (ha2.trans hb2.symm)]
    · -- connector: children are `inl w0` and at most one connector
      have hsub : Finset.univ.filter (fun z' => z' ≠ Sum.inr (Sum.inr ()) ∧
          par C π z' = Sum.inr (Sum.inl w0)) ⊆
          insert (Sum.inl w0) (Finset.univ.filter (fun z' => (∃ w, z' = Sum.inr (Sum.inl w) ∧
            (cand C π w).Nonempty ∧ prevOf C π w = w0))) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases a with a | a | a
        · left; simp only [par] at ha
          rw [Sum.inl_injective (Sum.inr_injective ha.2)]
        · right
          rcases par_conn_eq C π a _ ha.2 with ⟨h1, h2⟩ | ⟨_, h2⟩
          · exact ⟨a, rfl, h1, (Sum.inl_injective (Sum.inr_injective h2)).symm⟩
          · exact absurd h2.symm (Pn_ne_conn C π a w0)
        · exact absurd ha.1 (by simp)
      refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_insert_le _ _) ?_)
      apply Nat.succ_le_succ
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨wa, rfl, ha1, ha2⟩ := ha
      obtain ⟨wb, rfl, hb1, hb2⟩ := hb
      rw [uniq_prev C π ha1 hb1 ha2 hb2]
    · apply le_trans _ (by norm_num : 1 ≤ 2)
      apply Finset.card_le_one.2
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hr : ∀ (a : Nd V), a ≠ Sum.inr (Sum.inr ()) → par C π a = Sum.inr (Sum.inr r0) →
          ∃ w', a = Sum.inr (Sum.inl w') ∧ ¬ (cand C π w').Nonempty ∧
            Pn C π w' = Sum.inr (Sum.inr ()) := by
        intro a hne h
        rcases a with a | a | a
        · simp [par] at h
        · rcases par_conn_eq C π a _ h with ⟨_, h2⟩ | ⟨h1, h2⟩
          · simp at h2
          · exact ⟨a, rfl, h1, by rw [← h2]⟩
        · exact absurd (by cases a; rfl) hne
      obtain ⟨wa, rfl, ha1, ha2⟩ := hr a ha.1 ha.2
      obtain ⟨wb, rfl, hb1, hb2⟩ := hr b hb.1 hb.2
      rw [uniq_noPrev C π ha1 hb1 (ha2.trans hb2.symm)]

end Main


open Classical in
theorem binTD_exists (I : Instance) (ω : ℕ)
    (hTW : RobertsonSeymour1986.GM5.TreewidthLE (auxGraph I) ω) :
    ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T) (t : SimpleGraph T)
      (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
      (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n)),
      IsRootedBinaryTD I t X' rt par ∧ IsPartitionData I X' J Ip ∧
      (∀ z, (X' z).card ≤ ω + 1) ∧ Fintype.card T = 2 * (I.n + I.m) + 1 := by
  obtain ⟨rk, C, π, hrk, hCv, hCr, hCc, hπ, hclq⟩ := TAElim.elim_of_td (auxGraph I) ω hTW
  let Bd := Finset.univ.sup rk + 1
  have hBd : ∀ v, rk v < Bd := fun v => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  have hedge : ∀ a b, (auxGraph I).Adj a b → ∃ v, a ∈ C v ∧ b ∈ C v := by
    intro a b hab
    obtain ⟨v, hv⟩ := hclq {a, b} ⟨a, by simp⟩ (by
      intro u hu w hw huw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact absurd rfl huw
      · exact hab
      · exact hab.symm
      · exact absurd rfl huw)
    exact ⟨v, hv (by simp), hv (by simp)⟩
  obtain ⟨hTD, hrt, hadj, hreach, hbin⟩ := binTD_props rk C π hrk hCv hCr hπ Bd hBd
    (auxGraph I) hedge
  -- partition data: each edge `(i, j)` is assigned to one clique node
  have hij : ∀ i j, i ∈ I.e j → ∃ v, Sum.inl i ∈ C v ∧ Sum.inr j ∈ C v := by
    intro i j h
    exact hedge _ _ (by simpa [auxGraph] using h)
  let cv : Fin I.n → Fin I.m → (Fin I.n ⊕ Fin I.m) := fun i j =>
    if h : i ∈ I.e j then Classical.choose (hij i j h) else Sum.inl i
  have hcv : ∀ i j, i ∈ I.e j → Sum.inl i ∈ C (cv i j) ∧ Sum.inr j ∈ C (cv i j) := by
    intro i j h
    simp only [cv, dif_pos h]
    exact Classical.choose_spec (hij i j h)
  let J : Fin I.n → Nd (Fin I.n ⊕ Fin I.m) → Finset (Fin I.m) := fun i z =>
    Finset.univ.filter (fun j => i ∈ I.e j ∧ (Sum.inl (cv i j) : Nd _) = z)
  let Ip : Fin I.m → Nd (Fin I.n ⊕ Fin I.m) → Finset (Fin I.n) := fun j z =>
    Finset.univ.filter (fun i => i ∈ I.e j ∧ (Sum.inl (cv i j) : Nd _) = z)
  refine ⟨Nd (Fin I.n ⊕ Fin I.m), inferInstance, inferInstance, TAPP.ppGraph (par C π), B C π,
    Sum.inr (Sum.inr ()), par C π, J, Ip, ⟨hTD, hrt, hadj, hreach, hbin⟩, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i z j hj
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨h1, rfl⟩ := hj
      exact ⟨h1, hcv i j h1⟩
    · intro i z z' hne
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
    · intro i j h
      exact ⟨Sum.inl (cv i j), by simp [J, h]⟩
    · intro j z i hi
      simp only [Ip, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, hcv i j h1⟩
    · intro j z z' hne
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [Ip, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
    · intro j i h
      exact ⟨Sum.inl (cv i j), by simp [Ip, h]⟩
  · intro z
    rcases z with v | w | u
    · exact hCc v
    · simp only [B]; split_ifs
      · exact hCc _
      · simp
    · simp [B]
  · simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    ring

end TABin

namespace TAJT

open Finset

variable {n : ℕ}

/-- Restriction of a Boolean assignment to `D` (padded with `false`). -/
def rs (D : Finset (Fin n)) (z : Fin n → Bool) : Fin n → Bool :=
  fun u => if u ∈ D then z u else false

/-- Marginal of a function on assignments, on the coordinates `D`. -/
noncomputable def marg (D : Finset (Fin n)) (f : (Fin n → Bool) → ℝ) (c : Fin n → Bool) : ℝ :=
  ∑ z, if rs D z = c then f z else 0

theorem rs_rs {D D' : Finset (Fin n)} (h : D ⊆ D') (z : Fin n → Bool) :
    rs D (rs D' z) = rs D z := by
  funext u
  simp only [rs]
  by_cases hu : u ∈ D
  · simp [hu, h hu]
  · simp [hu]

theorem rs_idem (D : Finset (Fin n)) (z : Fin n → Bool) : rs D (rs D z) = rs D z :=
  rs_rs subset_rfl z

theorem marg_marg {D D' : Finset (Fin n)} (h : D ⊆ D') (f : (Fin n → Bool) → ℝ)
    (c : Fin n → Bool) :
    marg D f c = ∑ c', if rs D c' = c then marg D' f c' else 0 := by
  unfold marg
  have : ∀ c', (if rs D c' = c then ∑ z, (if rs D' z = c' then f z else 0) else 0) =
      ∑ z, (if rs D' z = c' then (if rs D c' = c then f z else 0) else 0) := by
    intro c'
    split_ifs with h1
    · apply Finset.sum_congr rfl; intro z _; split_ifs <;> rfl
    · symm; apply Finset.sum_eq_zero; intro z _; split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun c' _ => this c'), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_ite_eq]
  simp [rs_rs h]

theorem marg_supp (D : Finset (Fin n)) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ a, rs D a ≠ a → f a = 0) (c : Fin n → Bool) : marg D f c = f c := by
  unfold marg
  by_cases hc : rs D c = c
  · rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro z _ hz
      split_ifs with h1
      · apply hf; rw [h1]; exact fun h => hz h.symm
      · rfl
    · simp
  · rw [hf c hc]
    apply Finset.sum_eq_zero
    intro z _
    split_ifs with h1
    · apply hf
      intro h2
      apply hc
      rw [← h1, rs_idem]
    · rfl

theorem marg_nonneg (D : Finset (Fin n)) (f : (Fin n → Bool) → ℝ) (hf : ∀ a, 0 ≤ f a)
    (c : Fin n → Bool) : 0 ≤ marg D f c := by
  unfold marg
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact hf z
  · exact le_rfl

theorem le_marg (D : Finset (Fin n)) (f : (Fin n → Bool) → ℝ) (hf : ∀ a, 0 ≤ f a)
    (z : Fin n → Bool) : f z ≤ marg D f (rs D z) := by
  unfold marg
  have : f z = if rs D z = rs D z then f z else 0 := by simp
  rw [this]
  apply Finset.single_le_sum (f := fun z' => if rs D z' = rs D z then f z' else 0)
  · intro z' _
    split_ifs
    · exact hf z'
    · exact le_rfl
  · exact Finset.mem_univ z

theorem marg_empty (f : (Fin n → Bool) → ℝ) (c : Fin n → Bool) :
    marg ∅ f c = if (fun _ => false) = c then ∑ z, f z else 0 := by
  unfold marg
  have : ∀ z : Fin n → Bool, rs ∅ z = fun _ => false := by
    intro z; funext u; simp [rs]
  simp only [this]
  split_ifs <;> simp

/-- Splitting a sum over assignments along one coordinate. -/
theorem sum_split (v : Fin n) (f : (Fin n → Bool) → ℝ) :
    ∑ z, f z = ∑ z ∈ univ.filter (fun z => z v = false),
      (f z + f (Function.update z v true)) := by
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun z => z v = false)]
  congr 1
  apply Finset.sum_nbij' (fun z => Function.update z v false) (fun z => Function.update z v true)
  · intro z hz; simp
  · intro z hz; simp at hz ⊢
  · intro z hz
    have hz' : z v = true := by simpa using hz
    funext u
    by_cases hu : u = v
    · subst hu; simp [hz']
    · simp [Function.update_of_ne hu]
  · intro z hz
    have hz' : z v = false := by simpa using hz
    funext u
    by_cases hu : u = v
    · subst hu; simp [hz']
    · simp [Function.update_of_ne hu]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false] at hz
    congr 1
    funext u
    by_cases hu : u = v
    · subst hu; simp [hz]
    · simp [Function.update_of_ne hu]

theorem rs_update_of_not_mem (D : Finset (Fin n)) (z : Fin n → Bool) (v : Fin n) (b : Bool)
    (hv : v ∉ D) : rs D (Function.update z v b) = rs D z := by
  funext u
  simp only [rs]
  split_ifs with hu
  · have : u ≠ v := fun h => hv (h ▸ hu)
    simp [Function.update_of_ne this]
  · rfl

/-- Characterisation of `rs C z = c` through the separator `C.erase v`. -/
theorem rs_eq_iff (C : Finset (Fin n)) (v : Fin n) (hv : v ∈ C) (z c : Fin n → Bool)
    (hc : rs C c = c) :
    rs C z = c ↔ rs (C.erase v) z = rs (C.erase v) c ∧ z v = c v := by
  constructor
  · intro h
    subst h
    refine ⟨(rs_rs (Finset.erase_subset v C) z).symm, ?_⟩
    simp [rs, hv]
  · rintro ⟨h1, h2⟩
    funext u
    by_cases huv : u = v
    · subst huv
      have : rs C c u = c u := by rw [hc]
      simp only [rs, hv, if_true] at this ⊢
      exact h2
    · by_cases huC : u ∈ C
      · have hu : u ∈ C.erase v := Finset.mem_erase.2 ⟨huv, huC⟩
        have := congrFun h1 u
        simp only [rs, hu, if_true] at this
        simp only [rs, huC, if_true]
        exact this
      · have : rs C c u = c u := by rw [hc]
        simp only [rs, huC, if_false] at this ⊢
        exact this

/-- The separator marginal is the sum of the two extensions. -/
theorem marg_pair (C : Finset (Fin n)) (v : Fin n) (hv : v ∈ C) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ a, rs C a ≠ a → f a = 0) (z : Fin n → Bool) :
    marg (C.erase v) f (rs (C.erase v) z) =
      f (rs C (Function.update z v false)) + f (rs C (Function.update z v true)) := by
  have hvS : v ∉ C.erase v := Finset.notMem_erase v C
  unfold marg
  rw [sum_split v]
  set a0 := rs C (Function.update z v false) with ha0
  have ha0v : a0 v = false := by simp [ha0, rs, hv]
  have ha0C : rs C a0 = a0 := by rw [ha0, rs_idem]
  have ha0S : rs (C.erase v) a0 = rs (C.erase v) z := by
    rw [ha0, rs_rs (Finset.erase_subset v C), rs_update_of_not_mem _ _ _ _ hvS]
  have ha0t : Function.update a0 v true = rs C (Function.update z v true) := by
    funext u
    by_cases huv : u = v
    · subst huv; simp [rs, hv]
    · simp only [Function.update_of_ne huv, ha0, rs]
  rw [Finset.sum_eq_single a0]
  · rw [rs_update_of_not_mem _ _ _ _ hvS, ha0S, ha0t]
    simp
  · intro a ha hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [rs_update_of_not_mem _ _ _ _ hvS]
    split_ifs with h1
    · -- `a` agrees with `z` on the separator but differs from `a0`
      have hnot : rs C a ≠ a := by
        intro hC
        apply hne
        rw [← hC, rs_eq_iff C v hv a a0 ha0C]
        refine ⟨by rw [h1, ha0S], ?_⟩
        rw [ha, ha0v]
      have hnot' : rs C (Function.update a v true) ≠ Function.update a v true := by
        intro hC
        apply hnot
        funext u
        by_cases huC : u ∈ C
        · simp [rs, huC]
        · have := congrFun hC u
          have huv : u ≠ v := fun h => huC (h ▸ hv)
          simp only [rs, huC, if_false, Function.update_of_ne huv] at this
          simp only [rs, huC, if_false]
          exact this
      rw [hf a hnot, hf _ hnot']
      simp
    · simp
  · intro h
    exfalso; apply h
    simp [ha0v]

/-- Gluing locally consistent distributions along an elimination ordering. -/
theorem glue (rk : Fin n → ℕ) (hrk : Function.Injective rk) (C : Fin n → Finset (Fin n))
    (hCv : ∀ v, v ∈ C v) (hCr : ∀ v, ∀ u ∈ C v, rk v ≤ rk u) (π : Fin n → Fin n)
    (hπ : ∀ v, ((C v).erase v).Nonempty → rk v < rk (π v) ∧ (C v).erase v ⊆ C (π v))
    (lam : Fin n → (Fin n → Bool) → ℝ) (hnn : ∀ v a, 0 ≤ lam v a)
    (hsupp : ∀ v a, rs (C v) a ≠ a → lam v a = 0) (hsum : ∀ v, ∑ a, lam v a = 1)
    (hcons : ∀ v, ((C v).erase v).Nonempty → ∀ c,
      marg ((C v).erase v) (lam v) c = marg ((C v).erase v) (lam (π v)) c) :
    ∃ μ : (Fin n → Bool) → ℝ, (∀ z, 0 ≤ μ z) ∧ (∑ z, μ z = 1) ∧
      ∀ v c, marg (C v) μ c = lam v c := by
  classical
  let P : ℕ → Prop := fun θ => ∃ μ : (Fin n → Bool) → ℝ, (∀ z, 0 ≤ μ z) ∧ (∑ z, μ z = 1) ∧
    (∀ z, (∃ u, rk u < θ ∧ z u = true) → μ z = 0) ∧
    ∀ v, θ ≤ rk v → ∀ c, marg (C v) μ c = lam v c
  let B := Finset.univ.sup rk + 1
  have hB : ∀ v, rk v < B := fun v => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  have base : P B := by
    refine ⟨fun z => if z = (fun _ => false) then 1 else 0, ?_, ?_, ?_, ?_⟩
    · intro z; dsimp only; split_ifs <;> norm_num
    · simp
    · rintro z ⟨u, _, hu⟩
      have : z ≠ fun _ => false := by
        intro h; rw [h] at hu; exact Bool.false_ne_true hu
      simp [this]
    · intro v hv; exact absurd hv (Nat.not_le.2 (hB v))
  have step : ∀ θ, P (θ + 1) → P θ := by
    intro θ ⟨μ, hμ0, hμ1, hμs, hμm⟩
    by_cases hex : ∃ v0, rk v0 = θ
    swap
    · push Not at hex
      refine ⟨μ, hμ0, hμ1, fun z ⟨u, hu, hzu⟩ => hμs z ⟨u, by omega, hzu⟩, ?_⟩
      intro v hv c
      apply hμm v _ c
      have := hex v
      omega
    obtain ⟨v0, hv0⟩ := hex
    set S := (C v0).erase v0 with hS
    have hv0C := hCv v0
    have hv0S : v0 ∉ S := Finset.notMem_erase v0 (C v0)
    let m : (Fin n → Bool) → ℝ := fun c => marg S (lam v0) c
    -- (F1) the separator marginal of `μ` is `m`
    have F1 : ∀ c, marg S μ c = m c := by
      intro c
      by_cases hSne : S.Nonempty
      · obtain ⟨hlt, hsub⟩ := hπ v0 hSne
        have hm := hμm (π v0) (by omega)
        rw [marg_marg hsub μ c]
        simp only [m]
        rw [hcons v0 hSne c, marg_marg hsub (lam (π v0)) c]
        apply Finset.sum_congr rfl
        intro c' _
        rw [hm c', marg_supp _ _ (hsupp (π v0)) c']
      · rw [Finset.not_nonempty_iff_eq_empty] at hSne
        simp only [m]
        rw [hSne, marg_empty, marg_empty, hμ1, hsum v0]
    -- (F3) `μ` vanishes where `m` does
    have F3 : ∀ z, m (rs S z) = 0 → μ z = 0 := by
      intro z hz
      have h1 := le_marg S μ hμ0 z
      rw [F1, hz] at h1
      exact le_antisymm h1 (hμ0 z)
    have hlam_le : ∀ c, lam v0 c ≤ m (rs S c) := fun c => le_marg S (lam v0) (hnn v0) c
    let μ' : (Fin n → Bool) → ℝ := fun z =>
      μ (Function.update z v0 false) * lam v0 (rs (C v0) z) / m (rs S z)
    have hm0 : ∀ c, 0 ≤ m c := fun c => marg_nonneg S (lam v0) (hnn v0) c
    have F0 : ∀ z, 0 ≤ μ' z := fun z =>
      div_nonneg (mul_nonneg (hμ0 _) (hnn _ _)) (hm0 _)
    have hμv0 : ∀ z, z v0 = true → μ z = 0 := by
      intro z hz; exact hμs z ⟨v0, by omega, hz⟩
    have hzz : ∀ z : Fin n → Bool, z v0 = false → Function.update z v0 false = z := by
      intro z hz
      funext u; by_cases hu : u = v0
      · subst hu; simp [hz]
      · simp [Function.update_of_ne hu]
    -- (F4) marginals on sets avoiding `v0` are unchanged
    have F4 : ∀ D : Finset (Fin n), v0 ∉ D → ∀ c, marg D μ' c = marg D μ c := by
      intro D hD c
      unfold marg
      rw [sum_split v0, sum_split v0]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [rs_update_of_not_mem _ _ _ _ hD, hμv0 (Function.update z v0 true) (by simp)]
      split_ifs with hc
      · simp only [μ']
        rw [Function.update_idem, hzz z hz, rs_update_of_not_mem _ _ _ _ hv0S, ← add_div,
          ← mul_add]
        have hpair := marg_pair (C v0) v0 hv0C (lam v0) (hsupp v0) z
        rw [← hS, hzz z hz] at hpair
        rw [← hpair, add_zero]
        by_cases hmz : m (rs S z) = 0
        · rw [F3 z hmz]; simp
        · field_simp; rfl
      · simp
    -- (F5) the new marginal
    have F5 : ∀ c, marg (C v0) μ' c = lam v0 c := by
      intro c
      by_cases hc : rs (C v0) c = c
      swap
      · rw [hsupp v0 c hc]
        unfold marg
        apply Finset.sum_eq_zero
        intro z _
        split_ifs with h
        · exfalso; apply hc; rw [← h, rs_idem]
        · rfl
      have hval : ∀ z, rs (C v0) z = c → μ' z =
          μ (Function.update z v0 false) * (lam v0 c / m (rs S c)) := by
        intro z hz
        simp only [μ']
        have : rs S z = rs S c := by
          rw [← hz, hS, rs_rs (Finset.erase_subset v0 (C v0))]
        rw [hz, this]
        ring
      have hsum' : (∑ z, if rs (C v0) z = c then μ (Function.update z v0 false) else 0) =
          m (rs S c) := by
        rw [← F1]
        unfold marg
        rw [sum_split v0, sum_split v0]
        apply Finset.sum_congr rfl
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rw [hμv0 (Function.update z v0 true) (by simp), rs_update_of_not_mem _ _ _ _ hv0S,
          Function.update_idem, hzz z hz]
        have ha := rs_eq_iff (C v0) v0 hv0C z c hc
        have hb := rs_eq_iff (C v0) v0 hv0C (Function.update z v0 true) c hc
        rw [← hS] at ha hb
        rw [rs_update_of_not_mem _ _ _ _ hv0S] at hb
        simp only [Function.update_self] at hb
        by_cases h1 : rs S z = rs S c
        · cases hcv : c v0
          · have e1 : rs (C v0) z = c := ha.2 ⟨h1, by rw [hz, hcv]⟩
            have e2 : ¬ rs (C v0) (Function.update z v0 true) = c := by
              intro h; have := (hb.1 h).2; rw [hcv] at this; exact Bool.noConfusion this
            simp [e1, e2, h1]
          · have e1 : ¬ rs (C v0) z = c := by
              intro h; have := (ha.1 h).2; rw [hz, hcv] at this; exact Bool.noConfusion this
            have e2 : rs (C v0) (Function.update z v0 true) = c := hb.2 ⟨h1, by rw [hcv]⟩
            simp [e1, e2, h1]
        · have e1 : ¬ rs (C v0) z = c := fun h => h1 (ha.1 h).1
          have e2 : ¬ rs (C v0) (Function.update z v0 true) = c := fun h => h1 (hb.1 h).1
          simp [e1, e2, h1]
      unfold marg
      have : (∑ z, if rs (C v0) z = c then μ' z else 0) =
          (∑ z, if rs (C v0) z = c then μ (Function.update z v0 false) else 0) *
            (lam v0 c / m (rs S c)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs with h
        · exact hval z h
        · simp
      rw [this, hsum']
      by_cases hmz : m (rs S c) = 0
      · have : lam v0 c = 0 := le_antisymm (by rw [← hmz]; exact hlam_le c) (hnn v0 c)
        rw [this, hmz]; simp
      · field_simp
    refine ⟨μ', F0, ?_, ?_, ?_⟩
    · have h1 := F4 ∅ (Finset.notMem_empty v0) (fun _ => false)
      rw [marg_empty, marg_empty] at h1
      simp only [if_true] at h1
      rw [h1, hμ1]
    · rintro z ⟨u, hu, hzu⟩
      have huv : u ≠ v0 := by intro h; subst h; omega
      simp only [μ']
      rw [hμs _ ⟨u, by omega, by rwa [Function.update_of_ne huv]⟩]
      simp
    · intro v hv c
      by_cases hvv : v = v0
      · subst hvv; exact F5 c
      · have hlt : θ + 1 ≤ rk v := by
          have : rk v ≠ θ := fun h => hvv (hrk (h.trans hv0.symm))
          omega
        have hv0Cv : v0 ∉ C v := by
          intro h
          have := hCr v v0 h
          omega
        rw [F4 (C v) hv0Cv c, hμm v hlt c]
  have all : ∀ k, k ≤ B → P (B - k) := by
    intro k
    induction k with
    | zero => intro _; simpa using base
    | succ k ih =>
      intro hk
      have := ih (by omega)
      have e : B - k = (B - (k + 1)) + 1 := by omega
      rw [e] at this
      exact step _ this
  obtain ⟨μ, h0, h1, _, h3⟩ := all B le_rfl
  exact ⟨μ, h0, h1, fun v c => h3 v (by simp) c⟩

end TAJT
namespace TALP

open TraceAdopt.LPReform

/-- A finite linear system indexed by arbitrary finite types, in Fin-matrix form. -/
theorem to_matrix {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (rowX : κ → Fin n → ℝ) (rowY : κ → ι → ℝ) (rhs : κ → ℝ) :
    ∃ (A' : Matrix (Fin (Fintype.card κ)) (Fin n ⊕ Fin (Fintype.card ι)) ℝ)
      (b' : Fin (Fintype.card κ) → ℝ),
      {x : Fin n → ℝ | ∃ y : Fin (Fintype.card ι) → ℝ, LinFeasible A' b' x y} =
        {x | ∃ y : ι → ℝ, ∀ r, rhs r ≤ (∑ i, rowX r i * x i) + ∑ j, rowY r j * y j} := by
  classical
  let eι := Fintype.equivFin ι
  let eκ := Fintype.equivFin κ
  refine ⟨fun r v => Sum.elim (fun i => rowX (eκ.symm r) i) (fun j => rowY (eκ.symm r) (eι.symm j)) v,
    fun r => rhs (eκ.symm r), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, LinFeasible, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨y', hy'⟩
    refine ⟨fun j => y' (eι j), fun r => ?_⟩
    have := hy' (eκ r)
    simp only [Equiv.symm_apply_apply] at this
    convert this using 2
    rw [← Equiv.sum_comp eι.symm]
    simp
  · rintro ⟨y, hy⟩
    refine ⟨fun j => y (eι.symm j), fun r => ?_⟩
    have := hy (eκ.symm r)
    convert this using 2
    rw [← Equiv.sum_comp eι]
    simp

theorem proj_convex {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (rowX : κ → Fin n → ℝ) (rowY : κ → ι → ℝ) (rhs : κ → ℝ) :
    Convex ℝ {x : Fin n → ℝ | ∃ y : ι → ℝ, ∀ r, rhs r ≤ (∑ i, rowX r i * x i) + ∑ j, rowY r j * y j} := by
  intro x hx x' hx' a b ha hb hab
  obtain ⟨y, hy⟩ := hx
  obtain ⟨y', hy'⟩ := hx'
  refine ⟨a • y + b • y', fun r => ?_⟩
  have h1 := hy r
  have h2 := hy' r
  have e : (∑ i, rowX r i * (a • x + b • x') i) + ∑ j, rowY r j * (a • y + b • y') j =
      a * ((∑ i, rowX r i * x i) + ∑ j, rowY r j * y j) +
        b * ((∑ i, rowX r i * x' i) + ∑ j, rowY r j * y' j) := by
    have e1 : ∀ i, rowX r i * (a • x + b • x') i = a * (rowX r i * x i) + b * (rowX r i * x' i) := by
      intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : ∀ j, rowY r j * (a • y + b • y') j = a * (rowY r j * y j) + b * (rowY r j * y' j) := by
      intro j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_congr rfl (fun j _ => e2 j),
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [e]
  have : rhs r = a * rhs r + b * rhs r := by rw [← add_mul, hab, one_mul]
  rw [this]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

end TALP

namespace TAP4

open TraceAdopt.LPReform TAJT

variable {n : ℕ}

/-- Real indicator vector of a Boolean assignment. -/
def bval (z : Fin n → Bool) : Fin n → ℝ := fun i => if z i then 1 else 0

theorem sum_sigma_fst {β : Fin n → Type} [∀ v, Fintype (β v)] (v : Fin n)
    (f : (Σ v, β v) → ℝ) :
    (∑ j, if j.1 = v then f j else 0) = ∑ a : β v, f ⟨v, a⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single v]
  · simp
  · intro w _ hw; simp [hw]
  · simp

theorem sum_subtype_dite (p : (Fin n → Bool) → Prop) [DecidablePred p]
    (g : {a // p a} → ℝ) :
    (∑ a : {a // p a}, g a) = ∑ a, if h : p a then g ⟨a, h⟩ else 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]
  have h2 : (∑ a ∈ Finset.univ.filter (fun a => ¬ p a), if h : p a then g ⟨a, h⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp [ha]
  rw [h2, add_zero]
  rw [Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  simp [a.2]

theorem sum_marg (D : Finset (Fin n)) (μ : (Fin n → Bool) → ℝ) (h : (Fin n → Bool) → ℝ) :
    (∑ a, h a * marg D μ a) = ∑ z, μ z * h (rs D z) := by
  unfold marg
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_eq_single (rs D z)]
  · simp [mul_comm]
  · intro a _ ha
    rw [if_neg (Ne.symm ha), mul_zero]
  · simp

/-- Auxiliary variables: one per node `v` and local assignment on `C v`. -/
abbrev Iota (C : Fin n → Finset (Fin n)) := Σ v : Fin n, {a : Fin n → Bool // rs (C v) a = a}

/-- Separator assignments. -/
abbrev Sep (C : Fin n → Finset (Fin n)) :=
  Σ v : Fin n, {c : Fin n → Bool // rs ((C v).erase v) c = c}

/-- Constraint indices. -/
abbrev Kappa (C : Fin n → Finset (Fin n)) :=
  Iota C ⊕ Iota C ⊕ (Fin n × Bool) ⊕ (Fin n × Bool) ⊕ (Sep C × Bool)

def sg (s : Bool) : ℝ := if s then 1 else -1

theorem sg_ne (s : Bool) : sg s ≠ 0 := by cases s <;> simp [sg]

def rowX (C : Fin n → Finset (Fin n)) : Kappa C → Fin n → ℝ
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (v, s)))) => fun i => if i = v then sg s else 0
  | _ => fun _ => 0

open Classical in
noncomputable def rowY (C : Fin n → Finset (Fin n)) (π : Fin n → Fin n)
    (Loc : Fin n → (Fin n → Bool) → Prop) : Kappa C → Iota C → ℝ
  | Sum.inl j => fun j' => if j' = j then 1 else 0
  | Sum.inr (Sum.inl j) => fun j' => if j' = j ∧ ¬ Loc j.1 j.2.1 then -1 else 0
  | Sum.inr (Sum.inr (Sum.inl (v, s))) => fun j' => if j'.1 = v then sg s else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (v, s)))) => fun j' =>
      if j'.1 = v ∧ j'.2.1 v = true then -sg s else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨v, c⟩, s)))) => fun j' =>
      if ((C v).erase v).Nonempty then
        sg s * ((if j'.1 = v ∧ rs ((C v).erase v) j'.2.1 = c.1 then 1 else 0) -
          (if j'.1 = π v ∧ rs ((C v).erase v) j'.2.1 = c.1 then 1 else 0))
      else 0

def rhs (C : Fin n → Finset (Fin n)) : Kappa C → ℝ
  | Sum.inr (Sum.inr (Sum.inl (_, s))) => sg s
  | _ => 0

/-- Reading the linear system. -/
theorem feas_iff (C : Fin n → Finset (Fin n)) (π : Fin n → Fin n)
    (Loc : Fin n → (Fin n → Bool) → Prop) (x : Fin n → ℝ) (y : Iota C → ℝ) :
    (∀ r, rhs C r ≤ (∑ i, rowX C r i * x i) + ∑ j, rowY C π Loc r j * y j) ↔
      (∀ j, 0 ≤ y j) ∧ (∀ j, ¬ Loc j.1 j.2.1 → y j ≤ 0) ∧
      (∀ v, (∑ j, if j.1 = v then y j else 0) = 1) ∧
      (∀ v, x v = ∑ j, if j.1 = v ∧ j.2.1 v = true then y j else 0) ∧
      (∀ v, ((C v).erase v).Nonempty → ∀ c, rs ((C v).erase v) c = c →
        (∑ j, if j.1 = v ∧ rs ((C v).erase v) j.2.1 = c then y j else 0) =
          ∑ j, if j.1 = π v ∧ rs ((C v).erase v) j.2.1 = c then y j else 0) := by
  classical
  simp only [Sum.forall, Prod.forall]
  have hR1 : ∀ j, (rhs C (Sum.inl j) ≤ (∑ i, rowX C (Sum.inl j) i * x i) +
      ∑ j', rowY C π Loc (Sum.inl j) j' * y j') ↔ 0 ≤ y j := by
    intro j
    simp [rhs, rowX, rowY]
  have hR2 : ∀ j, (rhs C (Sum.inr (Sum.inl j)) ≤ (∑ i, rowX C (Sum.inr (Sum.inl j)) i * x i) +
      ∑ j', rowY C π Loc (Sum.inr (Sum.inl j)) j' * y j') ↔ (¬ Loc j.1 j.2.1 → y j ≤ 0) := by
    intro j
    by_cases hL : Loc j.1 j.2.1
    · simp [rhs, rowX, rowY, hL]
    · simp [rhs, rowX, rowY, hL]
  have hsum3 : ∀ v s, (∑ j', rowY C π Loc (Sum.inr (Sum.inr (Sum.inl (v, s)))) j' * y j') =
      sg s * ∑ j, if j.1 = v then y j else 0 := by
    intro v s
    simp only [rowY, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hsum4 : ∀ v s, (∑ j', rowY C π Loc (Sum.inr (Sum.inr (Sum.inr (Sum.inl (v, s))))) j' * y j') =
      -(sg s * ∑ j, if j.1 = v ∧ j.2.1 v = true then y j else 0) := by
    intro v s
    simp only [rowY, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hx4 : ∀ v s, (∑ i, rowX C (Sum.inr (Sum.inr (Sum.inr (Sum.inl (v, s))))) i * x i) =
      sg s * x v := by
    intro v s
    simp [rowX]
  have hsum5 : ∀ v c s, (∑ j', rowY C π Loc (Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨v, c⟩, s))))) j' * y j') =
      if ((C v).erase v).Nonempty then
        sg s * ((∑ j, if j.1 = v ∧ rs ((C v).erase v) j.2.1 = c.1 then y j else 0) -
          ∑ j, if j.1 = π v ∧ rs ((C v).erase v) j.2.1 = c.1 then y j else 0) else 0 := by
    intro v c s
    simp only [rowY]
    split_ifs with hne
    · rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    · simp
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun j => (hR1 j).1 (h1 j), fun j => (hR2 j).1 (h2 j), ?_, ?_, ?_⟩
    · intro v
      have a := h3 v true
      have b := h3 v false
      rw [hsum3] at a b
      simp [rhs, rowX, sg] at a b
      linarith
    · intro v
      have a := h4 v true
      have b := h4 v false
      rw [hx4, hsum4] at a b
      simp [rhs, sg] at a b
      linarith
    · intro v hne c hc
      have a := h5 ⟨v, ⟨c, hc⟩⟩ true
      have b := h5 ⟨v, ⟨c, hc⟩⟩ false
      rw [hsum5] at a b
      simp [rhs, rowX, hne, sg] at a b
      linarith
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun j => (hR1 j).2 (h1 j), fun j => (hR2 j).2 (h2 j), ?_, ?_, ?_⟩
    · intro v s
      rw [hsum3, h3 v]
      simp [rhs, rowX]
    · intro v s
      rw [hx4, hsum4, ← h4 v]
      simp [rhs]
    · rintro ⟨v, c, hc⟩ s
      rw [hsum5]
      split_ifs with hne
      · rw [h5 v hne c hc]; simp [rhs, rowX]
      · simp [rhs, rowX]

end TAP4

namespace TAP4
open TraceAdopt.LPReform TAJT
theorem card_sub_le {n : ℕ} (D : Finset (Fin n)) :
    Fintype.card {a : Fin n → Bool // rs D a = a} ≤ 2 ^ D.card := by
  classical
  have : Fintype.card {a : Fin n → Bool // rs D a = a} ≤ Fintype.card (D → Bool) := by
    apply Fintype.card_le_of_injective (fun a => fun u => a.1 u.1)
    intro a b hab
    apply Subtype.ext
    rw [← a.2, ← b.2]
    funext u
    simp only [rs]
    split_ifs with hu
    · exact congrFun hab ⟨u, hu⟩
    · rfl
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using this


end TAP4


namespace TAP4
open TraceAdopt.LPReform TAJT

theorem ef_local {n : ℕ} {ι : Type} [Fintype ι] (Pk : ι → (Fin n → Bool) → Prop)
    (sp : ι → Finset (Fin n))
    (hdep : ∀ k z z', (∀ u ∈ sp k, z u = z' u) → (Pk k z ↔ Pk k z')) (ω : ℕ)
    (hTW : RobertsonSeymour1986.GM5.TreewidthLE (intersectionGraph sp) ω) :
    ∃ (N K : ℕ) (A' : Matrix (Fin K) (Fin n ⊕ Fin N) ℝ) (b' : Fin K → ℝ),
      n + N + K ≤ 13 * 2 ^ ω * (n + 1) ∧
      {x : Fin n → ℝ | ∃ y : Fin N → ℝ, LinFeasible A' b' x y} =
        convexHull ℝ (bval '' {z | ∀ k, Pk k z}) := by
  classical
  set F := bval '' {z : Fin n → Bool | ∀ k, Pk k z} with hF
  have h2pos : 1 ≤ 2 ^ ω := Nat.one_le_two_pow
  by_cases hbad : ∃ k, sp k = ∅ ∧ ¬ Pk k (fun _ => false)
  · obtain ⟨k, hk0, hkb⟩ := hbad
    refine ⟨0, 1, 0, fun _ => 1, ?_, ?_⟩
    · nlinarith
    · have hFe : F = ∅ := by
        ext x
        simp only [hF, Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_exists, not_and]
        intro z hz _
        exact hkb ((hdep k z _ (by simp [hk0])).1 (hz k))
      rw [hFe, convexHull_empty]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro y hy
      have := hy 0
      simp at this
      linarith
  push Not at hbad
  have hbad' : ∀ k, sp k = ∅ → ∀ z, Pk k z := by
    intro k hk z
    exact (hdep k _ z (by simp [hk])).1 (hbad k hk)
  obtain ⟨rk, C, π, hrk, hCv, hCr, hCc, hπ, hclq⟩ := TAElim.elim_of_td _ ω hTW
  let Loc : Fin n → (Fin n → Bool) → Prop := fun v a => ∀ k, sp k ⊆ C v → Pk k a
  have hrowC : ∀ k v (z : Fin n → Bool), sp k ⊆ C v → (Pk k (rs (C v) z) ↔ Pk k z) := by
    intro k v z hsub
    apply hdep
    intro u hu
    simp [rs, hsub hu]
  obtain ⟨A', b', hAb⟩ := TALP.to_matrix (rowX C) (rowY C π Loc) (rhs C)
  refine ⟨Fintype.card (Iota C), Fintype.card (Kappa C), A', b', ?_, ?_⟩
  · -- size
    have hI : Fintype.card (Iota C) ≤ n * (2 * 2 ^ ω) := by
      rw [Fintype.card_sigma]
      calc (∑ v, Fintype.card {a : Fin n → Bool // rs (C v) a = a})
          ≤ ∑ _v : Fin n, 2 * 2 ^ ω := by
            apply Finset.sum_le_sum
            intro v _
            refine le_trans (card_sub_le (C v)) ?_
            rw [← pow_succ']
            exact Nat.pow_le_pow_right (by norm_num) (hCc v)
        _ = n * (2 * 2 ^ ω) := by simp
    have hS : Fintype.card (Sep C) ≤ n * 2 ^ ω := by
      rw [Fintype.card_sigma]
      calc (∑ v, Fintype.card {c : Fin n → Bool // rs ((C v).erase v) c = c})
          ≤ ∑ _v : Fin n, 2 ^ ω := by
            apply Finset.sum_le_sum
            intro v _
            refine le_trans (card_sub_le _) ?_
            apply Nat.pow_le_pow_right (by norm_num)
            rw [Finset.card_erase_of_mem (hCv v)]
            have := hCc v
            omega
        _ = n * 2 ^ ω := by simp
    have hK : Fintype.card (Kappa C) = 2 * Fintype.card (Iota C) + 4 * n +
        2 * Fintype.card (Sep C) := by
      simp only [Kappa, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      ring
    rw [hK]
    nlinarith
  · rw [hAb]
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := (feas_iff C π Loc x y).1 hy
      let lam : Fin n → (Fin n → Bool) → ℝ := fun v a =>
        if h : rs (C v) a = a then y ⟨v, ⟨a, h⟩⟩ else 0
      have conv : ∀ v (g : (Fin n → Bool) → ℝ),
          (∑ a, g a * lam v a) = ∑ j : Iota C, if j.1 = v then g j.2.1 * y j else 0 := by
        intro v g
        rw [sum_sigma_fst v (fun j : Iota C => g j.2.1 * y j),
          sum_subtype_dite (fun a => rs (C v) a = a) (fun a => g a.1 * y ⟨v, a⟩)]
        apply Finset.sum_congr rfl
        intro a _
        simp only [lam]
        split_ifs <;> simp
      have hnn : ∀ v a, 0 ≤ lam v a := by
        intro v a; simp only [lam]; split_ifs
        · exact h1 _
        · exact le_rfl
      have hsupp : ∀ v a, rs (C v) a ≠ a → lam v a = 0 := by
        intro v a h; simp [lam, h]
      have hsum : ∀ v, ∑ a, lam v a = 1 := by
        intro v
        have := conv v (fun _ => 1)
        simp only [one_mul] at this
        rw [this]; exact h3 v
      have hmarg : ∀ (D : Finset (Fin n)) w c, marg D (lam w) c =
          ∑ j : Iota C, if j.1 = w ∧ rs D j.2.1 = c then y j else 0 := by
        intro D w c
        unfold marg
        have e1 : (∑ a, if rs D a = c then lam w a else 0) =
            ∑ a, (if rs D a = c then (1 : ℝ) else 0) * lam w a := by
          apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
        rw [e1, conv w]
        apply Finset.sum_congr rfl
        intro j _
        by_cases ha : j.1 = w <;> by_cases hb : rs D j.2.1 = c <;> simp [ha, hb]
      have hcons : ∀ v, ((C v).erase v).Nonempty → ∀ c,
          marg ((C v).erase v) (lam v) c = marg ((C v).erase v) (lam (π v)) c := by
        intro v hne c
        by_cases hc : rs ((C v).erase v) c = c
        · rw [hmarg, hmarg]; exact h5 v hne c hc
        · have hz : ∀ f, marg ((C v).erase v) f c = 0 := by
            intro f
            unfold marg
            apply Finset.sum_eq_zero
            intro a _
            split_ifs with h
            · exfalso; apply hc; rw [← h, rs_idem]
            · rfl
          rw [hz, hz]
      obtain ⟨μ, hμ0, hμ1, hμm⟩ := glue rk hrk C hCv hCr π hπ lam hnn hsupp hsum hcons
      have hx : x = ∑ z, μ z • bval z := by
        funext v
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h4 v]
        have e1 := conv v (fun a => bval a v)
        have e2 : (∑ j : Iota C, if j.1 = v ∧ j.2.1 v = true then y j else 0) =
            ∑ j : Iota C, if j.1 = v then bval j.2.1 v * y j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases ha : j.1 = v <;> by_cases hb : j.2.1 v = true <;> simp [ha, hb, bval]
        rw [e2, ← e1]
        have e3 : (∑ a, bval a v * lam v a) = ∑ a, bval a v * marg (C v) μ a := by
          apply Finset.sum_congr rfl; intro a _; rw [hμm]
        rw [e3, sum_marg]
        apply Finset.sum_congr rfl
        intro z _
        simp [bval, rs, hCv v]
      have hmem : ∀ z, 0 < μ z → bval z ∈ F := by
        intro z hz
        refine ⟨z, ?_, rfl⟩
        intro k
        by_cases hk : sp k = ∅
        · exact hbad' k hk z
        obtain ⟨v, hv⟩ := hclq (sp k) (Finset.nonempty_iff_ne_empty.2 hk)
          (by
            intro u hu w hw huw
            exact ⟨huw, k, hu, hw⟩)
        have hpos : 0 < lam v (rs (C v) z) := by
          have := le_marg (C v) μ hμ0 z
          rw [hμm] at this
          linarith
        have hL : Loc v (rs (C v) z) := by
          by_contra hL
          have := h2 ⟨v, ⟨rs (C v) z, rs_idem _ _⟩⟩ hL
          have e : lam v (rs (C v) z) = y ⟨v, ⟨rs (C v) z, rs_idem _ _⟩⟩ := by
            simp [lam, rs_idem]
          linarith
        exact (hrowC k v z hv).1 (hL k hv)
      have hfil : ∀ (f : (Fin n → Bool) → (Fin n → ℝ)),
          (∑ z, μ z • f z) = ∑ z ∈ Finset.univ.filter (fun z => 0 < μ z), μ z • f z := by
        intro f
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs with h
        · rfl
        · have : μ z = 0 := le_antisymm (not_lt.1 h) (hμ0 z)
          simp [this]
      have hfil1 : (∑ z ∈ Finset.univ.filter (fun z => 0 < μ z), μ z) = 1 := by
        rw [← hμ1, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs with h
        · rfl
        · exact (le_antisymm (not_lt.1 h) (hμ0 z)).symm
      rw [hx, hfil]
      apply (convex_convexHull ℝ F).sum_mem
      · intro z _; exact hμ0 z
      · exact hfil1
      · intro z hz
        exact subset_convexHull ℝ F (hmem z (by simpa using hz))
    · apply convexHull_min _ (TALP.proj_convex _ _ _)
      intro x hx
      obtain ⟨z, hzP, hz⟩ := hx
      let y : Iota C → ℝ := fun j => if j.2.1 = rs (C j.1) z then 1 else 0
      have key : ∀ w (P : (Fin n → Bool) → Prop) [DecidablePred P],
          (∑ j : Iota C, if j.1 = w ∧ P j.2.1 then y j else 0) =
            if P (rs (C w) z) then 1 else 0 := by
        intro w P _
        have e : (∑ j : Iota C, if j.1 = w ∧ P j.2.1 then y j else 0) =
            ∑ j : Iota C, if j.1 = w then (if P j.2.1 then y j else 0) else 0 := by
          apply Finset.sum_congr rfl; intro j _
          by_cases ha : j.1 = w <;> simp [ha]
        rw [e, sum_sigma_fst w (fun j : Iota C => if P j.2.1 then y j else 0)]
        rw [Finset.sum_eq_single ⟨rs (C w) z, rs_idem _ _⟩]
        · simp [y]
        · intro a _ ha
          have : a.1 ≠ rs (C w) z := fun h => ha (Subtype.ext h)
          simp [y, this]
        · simp
      refine ⟨y, (feas_iff C π Loc x y).2 ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · intro j; simp only [y]; split_ifs <;> norm_num
      · intro j hL
        simp only [y]
        split_ifs with h
        · exfalso; apply hL
          rw [h]
          intro k hk
          exact (hrowC k j.1 z hk).2 (hzP k)
        · exact le_rfl
      · intro v
        have := key v (fun _ => True)
        simpa using this
      · intro v
        rw [key v (fun a => a v = true)]
        conv_lhs => rw [← hz]
        simp [bval, rs, hCv v]
      · intro v hne c _
        rw [key v (fun a => rs ((C v).erase v) a = c), key (π v) (fun a => rs ((C v).erase v) a = c),
          rs_rs (Finset.erase_subset v (C v)), rs_rs (hπ v hne).2]


end TAP4

namespace TATW

theorem tw_comap {V W : Type} [DecidableEq V] [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) (G : SimpleGraph V) (G' : SimpleGraph W)
    (hle : ∀ a b, G.Adj a b → G'.Adj (f a) (f b)) (w : ℕ)
    (h : RobertsonSeymour1986.GM5.TreewidthLE G' w) : RobertsonSeymour1986.GM5.TreewidthLE G w := by
  classical
  obtain ⟨T, hT, t, X, ⟨htree, hcov, hedge, hpath⟩, hw⟩ := h
  refine ⟨T, hT, t, fun z => (X z).preimage f hf.injOn, ⟨htree, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    obtain ⟨z, hz⟩ := hcov (f v)
    exact ⟨z, by simpa using hz⟩
  · intro a b hab
    obtain ⟨z, hz1, hz2⟩ := hedge _ _ (hle a b hab)
    exact ⟨z, by simpa using hz1, by simpa using hz2⟩
  · intro s s' s'' p hp hs' v hv
    simp only [Finset.mem_inter, Finset.mem_preimage] at hv ⊢
    exact hpath s s' s'' p hp hs' (Finset.mem_inter.2 hv)
  · intro z
    refine le_trans ?_ (hw z)
    exact Finset.card_le_card_of_injOn f (fun x hx => by simpa using hx) hf.injOn

end TATW


open SimpleGraph

namespace TraceAdopt.LPReform

open SimpleGraph

/-- Sufficient condition for the path axiom (iii): bags containing a vertex are
walk-connected inside a tree. -/
theorem taTD_iii_of_walks {V T : Type} [DecidableEq V] {t : SimpleGraph T} (ht : t.IsAcyclic)
    (X : T → Finset V)
    (h : ∀ v a b, v ∈ X a → v ∈ X b → ∃ w : t.Walk a b, ∀ c ∈ w.support, v ∈ X c) :
    ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s' := by
  classical
  intro s s' s'' p hp hs' v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨w, hw⟩ := h v s s'' hv.1 hv.2
  have heq : (⟨w.bypass, w.bypass_isPath⟩ : t.Path s s'') = ⟨p, hp⟩ :=
    (ht.subsingleton_path s s'').elim _ _
  have hq : w.bypass = p := congrArg Subtype.val heq
  apply hw
  apply w.support_bypass_subset_support
  rw [hq]; exact hs'

theorem taTD_walks_of_iii {V T : Type} [DecidableEq V] {t : SimpleGraph T} (ht : t.Connected)
    (X : T → Finset V)
    (h : ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s') :
    ∀ v a b, v ∈ X a → v ∈ X b → ∃ w : t.Walk a b, ∀ c ∈ w.support, v ∈ X c := by
  classical
  intro v a b ha hb
  obtain ⟨w⟩ := ht.preconnected a b
  refine ⟨w.bypass, fun c hc => ?_⟩
  exact h a c b w.bypass w.bypass_isPath hc (Finset.mem_inter.2 ⟨ha, hb⟩)

section Leaves
variable {T : Type} (t : SimpleGraph T) {ι : Type} (sj : ι → T)

/-- The tree with one leaf `inr j` attached to `inl (sj j)` for each `j`. -/
def leafTree : SimpleGraph (T ⊕ ι) :=
  (t ⊕g (⊥ : SimpleGraph (ι))) ⊔ fromEdgeSet (Set.range fun j => s(Sum.inl (sj j), Sum.inr j))

theorem leafTree_adj_inl_inl (a b : T) : (leafTree t sj).Adj (Sum.inl a) (Sum.inl b) ↔ t.Adj a b := by
  simp [leafTree]

theorem leafTree_adj_inl_inr (j : ι) : (leafTree t sj).Adj (Sum.inl (sj j)) (Sum.inr j) := by
  simp [leafTree]

theorem leafTree_adj_inr_inl (j : ι) : (leafTree t sj).Adj (Sum.inr j) (Sum.inl (sj j)) :=
  (leafTree_adj_inl_inr t sj j).symm

/-- The embedding of `t` into the leaf tree. -/
def leafHom : t →g leafTree t sj where
  toFun := Sum.inl
  map_rel' := fun h => (leafTree_adj_inl_inl t sj _ _).2 h

/-- Lifting a walk of `t` to the leaf tree. -/
def liftWalk : ∀ {a b : T}, t.Walk a b → (leafTree t sj).Walk (Sum.inl a) (Sum.inl b)
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons ((leafTree_adj_inl_inl t sj _ _).2 h) (liftWalk p)

theorem liftWalk_support : ∀ {a b : T} (w : t.Walk a b) (c : T ⊕ ι),
    c ∈ (liftWalk t sj w).support → ∃ c0 ∈ w.support, c = Sum.inl c0
  | _, _, .nil, c, hc => by
    simp [liftWalk] at hc
    exact ⟨_, by simp, hc⟩
  | _, _, .cons h p, c, hc => by
    simp only [liftWalk, Walk.support_cons, List.mem_cons] at hc
    rcases hc with hc | hc
    · exact ⟨_, by simp, hc⟩
    · obtain ⟨c0, hc0, rfl⟩ := liftWalk_support p c hc
      exact ⟨c0, by simp [hc0], rfl⟩

theorem leafTree_connected (ht : t.Connected) : (leafTree t sj).Connected := by
  have hinl : ∀ a b : T, (leafTree t sj).Reachable (Sum.inl a) (Sum.inl b) := by
    intro a b
    obtain ⟨w⟩ := ht.preconnected a b
    exact ⟨w.map (leafHom t sj)⟩
  have hall : ∀ x : T ⊕ ι, ∃ a, (leafTree t sj).Reachable x (Sum.inl a) := by
    intro x
    cases x with
    | inl a => exact ⟨a, Reachable.refl _⟩
    | inr j => exact ⟨sj j, (leafTree_adj_inr_inl t sj j).reachable⟩
  have : Nonempty T := ht.nonempty
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hall x
  obtain ⟨b, hb⟩ := hall y
  exact ha.trans ((hinl a b).trans hb.symm)

theorem leafTree_isTree [Finite T] [Finite ι] (ht : t.IsTree) : (leafTree t sj).IsTree := by
  classical
  have hT := (isTree_iff_connected_and_card.1 ht).2
  rw [isTree_iff_connected_and_card]
  refine ⟨leafTree_connected t sj ht.connected, ?_⟩
  have hfinE : (t.edgeSet).Finite := Set.toFinite _
  have h1 : Nat.card ((t ⊕g (⊥ : SimpleGraph (ι))).edgeSet) = Nat.card t.edgeSet := by
    rw [Nat.card_congr (edgeSetSumEquiv), Nat.card_sum]
    simp
  have hL : (fromEdgeSet (Set.range fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι)))).edgeSet
      = Set.range fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι)) := by
    rw [edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨j, rfl⟩ := h
      simp
  have hinj : Function.Injective fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι)) := by
    intro j k hjk
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at hjk
    rcases hjk with ⟨_, h⟩ | h
    · exact h
    · simp at h
  have hdisj : Disjoint (t ⊕g (⊥ : SimpleGraph (ι))).edgeSet
      (Set.range fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι))) := by
    rw [Set.disjoint_left]
    rintro e he ⟨j, rfl⟩
    simp at he
  have hfin1 : ((t ⊕g (⊥ : SimpleGraph (ι))).edgeSet).Finite := Set.toFinite _
  have hfin2 : (Set.range fun j : ι => (s(Sum.inl (sj j), Sum.inr j) : Sym2 (T ⊕ ι))).Finite :=
    Set.finite_range _
  rw [Nat.card_coe_set_eq, leafTree, edgeSet_sup, hL, Set.ncard_union_eq hdisj hfin1 hfin2,
    Set.ncard_range_of_injective hinj, ← Nat.card_coe_set_eq, h1, Nat.card_sum, ← hT]
  simp
  ring

end Leaves

section P9
variable (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
  (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)

/-- Membership of a variable of (10) in the bag of node `z`. -/
def inBag (z : T) : Var10 I T → Prop
  | .s i => Sum.inl i ∈ X' z
  | .l p q => p ∈ X' z ∧ q ∈ X' z
  | .u i z' _ => z' = z ∧ Sum.inl i ∈ X' z
  | .ut i z' _ => Sum.inl i ∈ X' z' ∧ (z' = z ∨ (z' ≠ rt ∧ par z' = z))
  | .v j z' _ => z' = z ∧ Sum.inr j ∈ X' z
  | .vt j z' _ => Sum.inr j ∈ X' z' ∧ (z' = z ∨ (z' ≠ rt ∧ par z' = z))

/-- An injective encoding of the variables into a finite type. -/
def enc10 : Var10 I T → (Fin I.n) ⊕ ((Fin I.n ⊕ Fin I.m) × (Fin I.n ⊕ Fin I.m)) ⊕
    (Bool × Fin I.n × T × Fin (nu I + 1)) ⊕ (Bool × Fin I.m × T × Fin (nv I + 1))
  | .s i => Sum.inl i
  | .l p q => Sum.inr (Sum.inl (p, q))
  | .u i z τ => Sum.inr (Sum.inr (Sum.inl (true, i, z, τ)))
  | .ut i z τ => Sum.inr (Sum.inr (Sum.inl (false, i, z, τ)))
  | .v j z τ => Sum.inr (Sum.inr (Sum.inr (true, j, z, τ)))
  | .vt j z τ => Sum.inr (Sum.inr (Sum.inr (false, j, z, τ)))

theorem enc10_inj : Function.Injective (enc10 I (T := T)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [enc10]

instance : Finite (Var10 I T) := Finite.of_injective _ (enc10_inj I)

noncomputable instance : Fintype (Var10 I T) := Fintype.ofFinite _

end P9

theorem ta_prop9 (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
        (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
        (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
        (ω' : ℕ)
        (hX : IsRootedBinaryTD I t X' rt par) (hJ : IsPartitionData I X' J Ip)
        (hω : ∀ z, (X' z).card ≤ ω' + 1) :
        RobertsonSeymour1986.GM5.TreewidthLE (intersectionGraph10 I X' rt par J Ip)
          (9 * (ω' + 1) ^ 2 + 9 * (ω' + 1) * (Nat.log 2 (varthetaMax I) + 1)) := by
  classical
  obtain ⟨⟨htree, hvert, hedge, hpath⟩, hrt, hadj, _, hbin⟩ := hX
  have hwalks := taTD_walks_of_iii htree.connected X' hpath
  -- every constraint support lies in one bag
  have hsupp : ∀ k, ∃ z, ∀ x ∈ supp10 I X' rt par J Ip k, inBag I X' rt par z x := by
    intro k
    cases k with
    | a i z =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with hi
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨j, hj, rfl⟩ | ⟨τ, rfl⟩
        · exact ⟨(hJ.1 i z j hj).2.2, hi⟩
        · exact ⟨rfl, hi⟩
      · simp at hx
    | b i z =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with hi hr
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_singleton] at hx
        rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hiz'⟩, τ, rfl⟩) | rfl
        · exact ⟨rfl, hi⟩
        · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
          exact ⟨hiz', Or.inr hz'⟩
        · exact hi
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_filter] at hx
        rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hiz'⟩, τ, rfl⟩) | ⟨τ, rfl⟩
        · exact ⟨rfl, hi⟩
        · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
          exact ⟨hiz', Or.inr hz'⟩
        · exact ⟨hi, Or.inl rfl⟩
      · simp at hx
    | e j z =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with hj
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨i, hi, rfl⟩ | ⟨τ, rfl⟩
        · exact ⟨(hJ.2.2.2.1 j z i hi).2.1, hj⟩
        · exact ⟨rfl, hj⟩
      · simp at hx
    | f j z =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with hj hr
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty, or_false] at hx
        rcases hx with ⟨τ, rfl⟩ | ⟨z', ⟨hz', hjz'⟩, τ, rfl⟩
        · exact ⟨rfl, hj⟩
        · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
          exact ⟨hjz', Or.inr hz'⟩
      · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_filter] at hx
        rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hjz'⟩, τ, rfl⟩) | ⟨τ, rfl⟩
        · exact ⟨rfl, hj⟩
        · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
          exact ⟨hjz', Or.inr hz'⟩
        · exact ⟨hj, Or.inl rfl⟩
      · simp at hx
    | pair z p q =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with h
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.2.1, h.1⟩
      · simp at hx
    | triple z p q x0 =>
      refine ⟨z, fun x hx => ?_⟩
      simp only [supp10] at hx
      split_ifs at hx with h
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.2.1, h.2.2.1⟩
        · exact ⟨h.2.2.1, h.1⟩
      · simp at hx
  -- the bags
  let iso : Var10 I T → Prop := fun x => ∀ z, ¬ inBag I X' rt par z x
  let B : T ⊕ Var10 I T → Finset (Var10 I T) := fun a =>
    match a with
    | Sum.inl z => Finset.univ.filter (inBag I X' rt par z)
    | Sum.inr x => if iso x then {x} else ∅
  have hBl : ∀ z x, x ∈ B (Sum.inl z) ↔ inBag I X' rt par z x := by
    intro z x; simp [B]
  have hBr : ∀ y x, x ∈ B (Sum.inr y) ↔ x = y ∧ iso y := by
    intro y x
    by_cases h : iso y
    · simp [B, h]
    · simp [B, h]
  let sj : Var10 I T → T := fun _ => rt
  refine ⟨T ⊕ Var10 I T, inferInstance, leafTree t sj, B,
    ⟨leafTree_isTree t sj htree, ?_, ?_, ?_⟩, ?_⟩
  · -- cover
    intro x
    by_cases h : iso x
    · exact ⟨Sum.inr x, (hBr x x).2 ⟨rfl, h⟩⟩
    · simp only [iso, not_forall, not_not] at h
      obtain ⟨z, hz⟩ := h
      exact ⟨Sum.inl z, (hBl z x).2 hz⟩
  · -- edges
    intro x y hxy
    obtain ⟨_, k, hxk, hyk⟩ := hxy
    obtain ⟨z, hz⟩ := hsupp k
    exact ⟨Sum.inl z, (hBl z x).2 (hz x hxk), (hBl z y).2 (hz y hyk)⟩
  · -- path axiom
    apply taTD_iii_of_walks (leafTree_isTree t sj htree).isAcyclic B
    intro x a b ha hb
    cases a with
    | inr y =>
      obtain ⟨rfl, hiso⟩ := (hBr y x).1 ha
      cases b with
      | inl zb => exact absurd ((hBl zb x).1 hb) (hiso zb)
      | inr y' =>
        obtain ⟨rfl, _⟩ := (hBr y' x).1 hb
        exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact ha⟩
    | inl za =>
      cases b with
      | inr y =>
        obtain ⟨rfl, hiso⟩ := (hBr y x).1 hb
        exact absurd ((hBl za x).1 ha) (hiso za)
      | inl zb =>
        have ha' := (hBl za x).1 ha
        have hb' := (hBl zb x).1 hb
        -- a walk in `t` inside the node set of `x`
        suffices H : ∃ w : t.Walk za zb, ∀ c ∈ w.support, inBag I X' rt par c x by
          obtain ⟨w, hw⟩ := H
          refine ⟨liftWalk t sj w, fun c hc => ?_⟩
          obtain ⟨c0, hc0, rfl⟩ := liftWalk_support t sj w c hc
          exact (hBl c0 x).2 (hw c0 hc0)
        cases x with
        | s i => exact hwalks _ za zb ha' hb'
        | l p q =>
          obtain ⟨w0⟩ := htree.connected.preconnected za zb
          refine ⟨w0.bypass, fun c hc => ?_⟩
          have hsub := hpath za c zb w0.bypass w0.bypass_isPath hc
          exact ⟨hsub (Finset.mem_inter.2 ⟨ha'.1, hb'.1⟩), hsub (Finset.mem_inter.2 ⟨ha'.2, hb'.2⟩)⟩
        | u i z τ =>
          obtain ⟨rfl, hi⟩ := ha'
          obtain ⟨rfl, _⟩ := hb'
          exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact ⟨rfl, hi⟩⟩
        | v j z τ =>
          obtain ⟨rfl, hi⟩ := ha'
          obtain ⟨rfl, _⟩ := hb'
          exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact ⟨rfl, hi⟩⟩
        | ut i z τ =>
          obtain ⟨hiz, hza⟩ := ha'
          obtain ⟨_, hzb⟩ := hb'
          have hzz : inBag I X' rt par z (Var10.ut i z τ) := ⟨hiz, Or.inl rfl⟩
          have hzp : z ≠ rt → inBag I X' rt par (par z) (Var10.ut i z τ) :=
            fun h => ⟨hiz, Or.inr ⟨h, rfl⟩⟩
          rcases hza with rfl | ⟨hzr, rfl⟩ <;> rcases hzb with rfl | ⟨hzr', rfl⟩
          · exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hzz⟩
          · refine ⟨Walk.cons (hadj _ hzr') Walk.nil, fun c hc => ?_⟩
            simp at hc; rcases hc with rfl | rfl
            · exact hzz
            · exact hzp hzr'
          · refine ⟨Walk.cons (hadj _ hzr).symm Walk.nil, fun c hc => ?_⟩
            simp at hc; rcases hc with rfl | rfl
            · exact hzp hzr
            · exact hzz
          · exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hzp hzr⟩
        | vt j z τ =>
          obtain ⟨hiz, hza⟩ := ha'
          obtain ⟨_, hzb⟩ := hb'
          have hzz : inBag I X' rt par z (Var10.vt j z τ) := ⟨hiz, Or.inl rfl⟩
          have hzp : z ≠ rt → inBag I X' rt par (par z) (Var10.vt j z τ) :=
            fun h => ⟨hiz, Or.inr ⟨h, rfl⟩⟩
          rcases hza with rfl | ⟨hzr, rfl⟩ <;> rcases hzb with rfl | ⟨hzr', rfl⟩
          · exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hzz⟩
          · refine ⟨Walk.cons (hadj _ hzr') Walk.nil, fun c hc => ?_⟩
            simp at hc; rcases hc with rfl | rfl
            · exact hzz
            · exact hzp hzr'
          · refine ⟨Walk.cons (hadj _ hzr).symm Walk.nil, fun c hc => ?_⟩
            simp at hc; rcases hc with rfl | rfl
            · exact hzp hzr
            · exact hzz
          · exact ⟨Walk.nil, fun c hc => by simp at hc; subst hc; exact hzp hzr⟩
  · -- width
    have hlogu : nu I ≤ Nat.log 2 (varthetaMax I) := Nat.log_mono_right (le_max_left _ _)
    have hlogv : nv I ≤ Nat.log 2 (varthetaMax I) := by
      apply Nat.log_mono_right
      have h1 : Finset.univ.sup I.θ ≤ Finset.univ.sup (fun j => I.θ j - 1) + 1 := by
        apply Finset.sup_le
        intro j _
        have := Finset.le_sup (f := fun j => I.θ j - 1) (Finset.mem_univ j)
        omega
      have h2 : Finset.univ.sup (fun j => I.θ j - 1) ≤ varthetaMax I := le_max_right _ _
      omega
    set L := Nat.log 2 (varthetaMax I) with hL
    have cu : ∀ (A B : Finset (Var10 I T)) (a b : ℕ), A.card ≤ a → B.card ≤ b →
        (A ∪ B).card ≤ a + b := fun A B a b ha hb =>
      le_trans (Finset.card_union_le A B) (Nat.add_le_add ha hb)
    let F : T → Finset (Fin I.n) := fun z => Finset.univ.filter (fun i => Sum.inl i ∈ X' z)
    let G : T → Finset (Fin I.m) := fun z => Finset.univ.filter (fun j => Sum.inr j ∈ X' z)
    have hF : ∀ z, (F z).card ≤ ω' + 1 := by
      intro z
      refine le_trans ?_ (hω z)
      rw [← Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩]
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      simpa [F] using hi
    have hG : ∀ z, (G z).card ≤ ω' + 1 := by
      intro z
      refine le_trans ?_ (hω z)
      rw [← Finset.card_map ⟨Sum.inr, Sum.inr_injective⟩]
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      simpa [G] using hj
    intro a
    cases a with
    | inr y =>
      simp only [B]
      split_ifs <;> simp
    | inl z =>
      let Ls := (X' z ×ˢ X' z).image (fun pq => Var10.l (T := T) pq.1 pq.2)
      let Ss := (F z).image (Var10.s (T := T))
      let Uu := (F z ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.u p.1 z p.2)
      let Ut := (F z ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.ut p.1 z p.2)
      let Utc := (children rt par z).biUnion (fun z' =>
        (F z' ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.ut p.1 z' p.2))
      let Vv := (G z ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.v p.1 z p.2)
      let Vt := (G z ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.vt p.1 z p.2)
      let Vtc := (children rt par z).biUnion (fun z' =>
        (G z' ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.vt p.1 z' p.2))
      have hsub : B (Sum.inl z) ⊆ Ls ∪ Ss ∪ Uu ∪ Ut ∪ Utc ∪ Vv ∪ Vt ∪ Vtc := by
        intro x hx
        rw [hBl] at hx
        simp only [Finset.mem_union]
        cases x with
        | s i =>
          simp only [inBag] at hx
          left; left; left; left; left; left; right
          exact Finset.mem_image.2 ⟨i, by simpa [F] using hx, rfl⟩
        | l p q =>
          simp only [inBag] at hx
          left; left; left; left; left; left; left
          exact Finset.mem_image.2 ⟨(p, q), Finset.mem_product.2 hx, rfl⟩
        | u i z' τ =>
          simp only [inBag] at hx
          obtain ⟨rfl, hi⟩ := hx
          left; left; left; left; left; right
          exact Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩
        | ut i z' τ =>
          simp only [inBag] at hx
          obtain ⟨hi, rfl | ⟨hr, hp⟩⟩ := hx
          · left; left; left; left; right
            exact Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩
          · left; left; left; right
            refine Finset.mem_biUnion.2 ⟨z', ?_, Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩⟩
            simp [children, hr, hp]
        | v j z' τ =>
          simp only [inBag] at hx
          obtain ⟨rfl, hj⟩ := hx
          left; left; right
          exact Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩
        | vt j z' τ =>
          simp only [inBag] at hx
          obtain ⟨hj, rfl | ⟨hr, hp⟩⟩ := hx
          · left; right
            exact Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩
          · right
            refine Finset.mem_biUnion.2 ⟨z', ?_, Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩⟩
            simp [children, hr, hp]
      have hch : (children rt par z).card ≤ 2 := hbin z
      have bU : ∀ z', ((F z' ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image
          (fun p => Var10.ut (T := T) p.1 z' p.2)).card ≤ (ω' + 1) * (nu I + 1) := by
        intro z'
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hF z')
      have bV : ∀ z', ((G z' ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image
          (fun p => Var10.vt (T := T) p.1 z' p.2)).card ≤ (ω' + 1) * (nv I + 1) := by
        intro z'
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hG z')
      have b1 : Ls.card ≤ (ω' + 1) * (ω' + 1) := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product]
        exact Nat.mul_le_mul (hω z) (hω z)
      have b2 : Ss.card ≤ ω' + 1 := le_trans Finset.card_image_le (hF z)
      have b3 : Uu.card ≤ (ω' + 1) * (nu I + 1) := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hF z)
      have b4 : Ut.card ≤ (ω' + 1) * (nu I + 1) := bU z
      have b5 : Utc.card ≤ 2 * ((ω' + 1) * (nu I + 1)) := by
        refine le_trans Finset.card_biUnion_le ?_
        refine le_trans (Finset.sum_le_card_nsmul _ _ ((ω' + 1) * (nu I + 1)) (fun z' _ => bU z')) ?_
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ hch
      have b6 : Vv.card ≤ (ω' + 1) * (nv I + 1) := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hG z)
      have b7 : Vt.card ≤ (ω' + 1) * (nv I + 1) := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hG z)
      have b8 : Vtc.card ≤ 2 * ((ω' + 1) * (nv I + 1)) := by
        refine le_trans Finset.card_biUnion_le ?_
        refine le_trans (Finset.sum_le_card_nsmul _ _ ((ω' + 1) * (nv I + 1)) (fun z' _ => bV z')) ?_
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ hch
      have htot := cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _
        (cu _ _ _ _ b1 b2) b3) b4) b5) b6) b7) b8
      refine le_trans (Finset.card_le_card hsub) (le_trans htot ?_)
      have hu : (ω' + 1) * (nu I + 1) ≤ (ω' + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      have hv : (ω' + 1) * (nv I + 1) ≤ (ω' + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      have ha : ω' + 1 ≤ (ω' + 1) * (ω' + 1) := Nat.le_mul_of_pos_left _ (by omega)
      have e1 : (ω' + 1) ^ 2 = (ω' + 1) * (ω' + 1) := by ring
      have e2 : 9 * (ω' + 1) * (L + 1) = 9 * ((ω' + 1) * (L + 1)) := by ring
      rw [e1, e2]
      omega


theorem supp_inBag (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
    (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
    (hJ : IsPartitionData I X' J Ip) :
    ∀ k, ∃ z, ∀ x ∈ supp10 I X' rt par J Ip k, inBag I X' rt par z x := by
  classical
  intro k
  cases k with
  | a i z =>
    refine ⟨z, fun x hx => ?_⟩
    simp only [supp10] at hx
    split_ifs at hx with hi
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨j, hj, rfl⟩ | ⟨τ, rfl⟩
      · exact ⟨(hJ.1 i z j hj).2.2, hi⟩
      · exact ⟨rfl, hi⟩
    · simp at hx
  | b i z =>
    refine ⟨z, fun x hx => ?_⟩
    simp only [supp10] at hx
    split_ifs at hx with hi hr
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_filter, Finset.mem_singleton] at hx
      rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hiz'⟩, τ, rfl⟩) | rfl
      · exact ⟨rfl, hi⟩
      · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
        exact ⟨hiz', Or.inr hz'⟩
      · exact hi
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_filter] at hx
      rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hiz'⟩, τ, rfl⟩) | ⟨τ, rfl⟩
      · exact ⟨rfl, hi⟩
      · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
        exact ⟨hiz', Or.inr hz'⟩
      · exact ⟨hi, Or.inl rfl⟩
    · simp at hx
  | e j z =>
    refine ⟨z, fun x hx => ?_⟩
    simp only [supp10] at hx
    split_ifs at hx with hj
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨i, hi, rfl⟩ | ⟨τ, rfl⟩
      · exact ⟨(hJ.2.2.2.1 j z i hi).2.1, hj⟩
      · exact ⟨rfl, hj⟩
    · simp at hx
  | f j z =>
    refine ⟨z, fun x hx => ?_⟩
    simp only [supp10] at hx
    split_ifs at hx with hj hr
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty, or_false] at hx
      rcases hx with ⟨τ, rfl⟩ | ⟨z', ⟨hz', hjz'⟩, τ, rfl⟩
      · exact ⟨rfl, hj⟩
      · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
        exact ⟨hjz', Or.inr hz'⟩
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_filter] at hx
      rcases hx with (⟨τ, rfl⟩ | ⟨z', ⟨hz', hjz'⟩, τ, rfl⟩) | ⟨τ, rfl⟩
      · exact ⟨rfl, hj⟩
      · simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
        exact ⟨hjz', Or.inr hz'⟩
      · exact ⟨hj, Or.inl rfl⟩
    · simp at hx
  | pair z p q =>
    refine ⟨z, fun x hx => ?_⟩
    simp only [supp10] at hx
    split_ifs at hx with h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨h.1, h.2.1⟩
      · exact ⟨h.2.1, h.1⟩
    · simp at hx
  | triple z p q x0 =>
    refine ⟨z, fun x hx => ?_⟩
    simp only [supp10] at hx
    split_ifs at hx with h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨h.1, h.2.1⟩
      · exact ⟨h.2.1, h.2.2.1⟩
      · exact ⟨h.2.2.1, h.1⟩
    · simp at hx


open Classical in
theorem inBag_card (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
    (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T) (ω' : ℕ)
    (hbin : ∀ z, (Finset.univ.filter (fun z' => z' ≠ rt ∧ par z' = z)).card ≤ 2)
    (hω : ∀ z, (X' z).card ≤ ω' + 1) (z : T) :
    (Finset.univ.filter (inBag I X' rt par z)).card ≤
      9 * (ω' + 1) ^ 2 + 9 * (ω' + 1) * (Nat.log 2 (varthetaMax I) + 1) + 1 := by
  classical
  have hBl : ∀ z x, x ∈ Finset.univ.filter (inBag I X' rt par z) ↔ inBag I X' rt par z x := by
    intro z x; simp
  let B : T ⊕ Var10 I T → Finset (Var10 I T) := fun a =>
    match a with
    | Sum.inl z => Finset.univ.filter (inBag I X' rt par z)
    | Sum.inr x => ∅
  show (B (Sum.inl z)).card ≤ _
  have hlogu : nu I ≤ Nat.log 2 (varthetaMax I) := Nat.log_mono_right (le_max_left _ _)
  have hlogv : nv I ≤ Nat.log 2 (varthetaMax I) := by
    apply Nat.log_mono_right
    have h1 : Finset.univ.sup I.θ ≤ Finset.univ.sup (fun j => I.θ j - 1) + 1 := by
      apply Finset.sup_le
      intro j _
      have := Finset.le_sup (f := fun j => I.θ j - 1) (Finset.mem_univ j)
      omega
    have h2 : Finset.univ.sup (fun j => I.θ j - 1) ≤ varthetaMax I := le_max_right _ _
    omega
  set L := Nat.log 2 (varthetaMax I) with hL
  have cu : ∀ (A B : Finset (Var10 I T)) (a b : ℕ), A.card ≤ a → B.card ≤ b →
      (A ∪ B).card ≤ a + b := fun A B a b ha hb =>
    le_trans (Finset.card_union_le A B) (Nat.add_le_add ha hb)
  let F : T → Finset (Fin I.n) := fun z => Finset.univ.filter (fun i => Sum.inl i ∈ X' z)
  let G : T → Finset (Fin I.m) := fun z => Finset.univ.filter (fun j => Sum.inr j ∈ X' z)
  have hF : ∀ z, (F z).card ≤ ω' + 1 := by
    intro z
    refine le_trans ?_ (hω z)
    rw [← Finset.card_map ⟨Sum.inl, Sum.inl_injective⟩]
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    simpa [F] using hi
  have hG : ∀ z, (G z).card ≤ ω' + 1 := by
    intro z
    refine le_trans ?_ (hω z)
    rw [← Finset.card_map ⟨Sum.inr, Sum.inr_injective⟩]
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    simpa [G] using hj
  let Ls := (X' z ×ˢ X' z).image (fun pq => Var10.l (T := T) pq.1 pq.2)
  let Ss := (F z).image (Var10.s (T := T))
  let Uu := (F z ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.u p.1 z p.2)
  let Ut := (F z ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.ut p.1 z p.2)
  let Utc := (children rt par z).biUnion (fun z' =>
    (F z' ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image (fun p => Var10.ut p.1 z' p.2))
  let Vv := (G z ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.v p.1 z p.2)
  let Vt := (G z ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.vt p.1 z p.2)
  let Vtc := (children rt par z).biUnion (fun z' =>
    (G z' ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image (fun p => Var10.vt p.1 z' p.2))
  have hsub : B (Sum.inl z) ⊆ Ls ∪ Ss ∪ Uu ∪ Ut ∪ Utc ∪ Vv ∪ Vt ∪ Vtc := by
    intro x hx
    rw [hBl] at hx
    simp only [Finset.mem_union]
    cases x with
    | s i =>
      simp only [inBag] at hx
      left; left; left; left; left; left; right
      exact Finset.mem_image.2 ⟨i, by simpa [F] using hx, rfl⟩
    | l p q =>
      simp only [inBag] at hx
      left; left; left; left; left; left; left
      exact Finset.mem_image.2 ⟨(p, q), Finset.mem_product.2 hx, rfl⟩
    | u i z' τ =>
      simp only [inBag] at hx
      obtain ⟨rfl, hi⟩ := hx
      left; left; left; left; left; right
      exact Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩
    | ut i z' τ =>
      simp only [inBag] at hx
      obtain ⟨hi, rfl | ⟨hr, hp⟩⟩ := hx
      · left; left; left; left; right
        exact Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩
      · left; left; left; right
        refine Finset.mem_biUnion.2 ⟨z', ?_, Finset.mem_image.2 ⟨(i, τ), by simpa [F] using hi, rfl⟩⟩
        simp [children, hr, hp]
    | v j z' τ =>
      simp only [inBag] at hx
      obtain ⟨rfl, hj⟩ := hx
      left; left; right
      exact Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩
    | vt j z' τ =>
      simp only [inBag] at hx
      obtain ⟨hj, rfl | ⟨hr, hp⟩⟩ := hx
      · left; right
        exact Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩
      · right
        refine Finset.mem_biUnion.2 ⟨z', ?_, Finset.mem_image.2 ⟨(j, τ), by simpa [G] using hj, rfl⟩⟩
        simp [children, hr, hp]
  have hch : (children rt par z).card ≤ 2 := hbin z
  have bU : ∀ z', ((F z' ×ˢ (Finset.univ : Finset (Fin (nu I + 1)))).image
      (fun p => Var10.ut (T := T) p.1 z' p.2)).card ≤ (ω' + 1) * (nu I + 1) := by
    intro z'
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (hF z')
  have bV : ∀ z', ((G z' ×ˢ (Finset.univ : Finset (Fin (nv I + 1)))).image
      (fun p => Var10.vt (T := T) p.1 z' p.2)).card ≤ (ω' + 1) * (nv I + 1) := by
    intro z'
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (hG z')
  have b1 : Ls.card ≤ (ω' + 1) * (ω' + 1) := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product]
    exact Nat.mul_le_mul (hω z) (hω z)
  have b2 : Ss.card ≤ ω' + 1 := le_trans Finset.card_image_le (hF z)
  have b3 : Uu.card ≤ (ω' + 1) * (nu I + 1) := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (hF z)
  have b4 : Ut.card ≤ (ω' + 1) * (nu I + 1) := bU z
  have b5 : Utc.card ≤ 2 * ((ω' + 1) * (nu I + 1)) := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ ((ω' + 1) * (nu I + 1)) (fun z' _ => bU z')) ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _ hch
  have b6 : Vv.card ≤ (ω' + 1) * (nv I + 1) := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (hG z)
  have b7 : Vt.card ≤ (ω' + 1) * (nv I + 1) := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (hG z)
  have b8 : Vtc.card ≤ 2 * ((ω' + 1) * (nv I + 1)) := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ ((ω' + 1) * (nv I + 1)) (fun z' _ => bV z')) ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _ hch
  have htot := cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _ (cu _ _ _ _
    (cu _ _ _ _ b1 b2) b3) b4) b5) b6) b7) b8
  refine le_trans (Finset.card_le_card hsub) (le_trans htot ?_)
  have hu : (ω' + 1) * (nu I + 1) ≤ (ω' + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  have hv : (ω' + 1) * (nv I + 1) ≤ (ω' + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  have ha : ω' + 1 ≤ (ω' + 1) * (ω' + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : (ω' + 1) ^ 2 = (ω' + 1) * (ω' + 1) := by ring
  have e2 : 9 * (ω' + 1) * (L + 1) = 9 * ((ω' + 1) * (L + 1)) := by ring
  rw [e1, e2]
  omega


end TraceAdopt.LPReform


namespace TAEnc

open TraceAdopt.LPReform

section ConFin
variable (I : Instance) {T : Type} [Fintype T]

def encC : Con10 I T → (Bool × Fin I.n × T) ⊕ (Bool × Fin I.m × T) ⊕
    (T × (Fin I.n ⊕ Fin I.m) × (Fin I.n ⊕ Fin I.m)) ⊕
    (T × (Fin I.n ⊕ Fin I.m) × (Fin I.n ⊕ Fin I.m) × (Fin I.n ⊕ Fin I.m))
  | .a i z => Sum.inl (true, i, z)
  | .b i z => Sum.inl (false, i, z)
  | .e j z => Sum.inr (Sum.inl (true, j, z))
  | .f j z => Sum.inr (Sum.inl (false, j, z))
  | .pair z p q => Sum.inr (Sum.inr (Sum.inl (z, p, q)))
  | .triple z p q x => Sum.inr (Sum.inr (Sum.inr (z, p, q, x)))

theorem encC_inj : Function.Injective (encC I (T := T)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [encC]

instance : Finite (Con10 I T) := Finite.of_injective _ (encC_inj I)

noncomputable instance : Fintype (Con10 I T) := Fintype.ofFinite _

end ConFin

section
variable (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
  (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
  (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))

open Classical in
/-- The constraint of (10) with index `k`, evaluated at a valuation `φ`. -/
def clause (φ : Var10 I T → ℕ) : Con10 I T → Prop
  | .a i z => Sum.inl i ∈ X' z →
      bitVal (fun τ => φ (.u i z τ)) ≤ ∑ j ∈ J i z, I.r j i * φ (.l (Sum.inr j) (Sum.inl i))
  | .b i z => (Sum.inl i ∈ X' z → ¬ IsSubtreeRoot I X' rt par (Sum.inl i) z →
        bitVal (fun τ => φ (.ut i z τ)) ≤ bitVal (fun τ => φ (.u i z τ)) +
          ∑ z' ∈ (children rt par z).filter (fun z' => Sum.inl i ∈ X' z'),
            bitVal (fun τ => φ (.ut i z' τ))) ∧
      (IsSubtreeRoot I X' rt par (Sum.inl i) z →
        I.c i ≤ bitVal (fun τ => φ (.u i z τ)) +
          (∑ z' ∈ (children rt par z).filter (fun z' => Sum.inl i ∈ X' z'),
            bitVal (fun τ => φ (.ut i z' τ))) + I.c i * φ (.s i))
  | .e j z => Sum.inr j ∈ X' z →
      bitVal (fun τ => φ (.v j z τ)) ≤ ∑ i ∈ Ip j z, φ (.l (Sum.inl i) (Sum.inr j))
  | .f j z => (Sum.inr j ∈ X' z → ¬ IsSubtreeRoot I X' rt par (Sum.inr j) z →
        bitVal (fun τ => φ (.vt j z τ)) ≤ bitVal (fun τ => φ (.v j z τ)) +
          ∑ z' ∈ (children rt par z).filter (fun z' => Sum.inr j ∈ X' z'),
            bitVal (fun τ => φ (.vt j z' τ))) ∧
      (IsSubtreeRoot I X' rt par (Sum.inr j) z →
        I.θ j - 1 ≤ bitVal (fun τ => φ (.v j z τ)) +
          ∑ z' ∈ (children rt par z).filter (fun z' => Sum.inr j ∈ X' z'),
            bitVal (fun τ => φ (.vt j z' τ)))
  | .pair z p q => p ∈ X' z → q ∈ X' z → p ≠ q → φ (.l p q) + φ (.l q p) = 1
  | .triple z p q x => p ∈ X' z → q ∈ X' z → x ∈ X' z → p ≠ q → q ≠ x → p ≠ x →
      φ (.l p q) + φ (.l q x) + φ (.l x p) ≤ 2

theorem feas_iff_clauses (φ : Var10 I T → ℕ) (hb : ∀ x, φ x ≤ 1) :
    BiLP10Feasible I X' rt par J Ip (fun i => φ (.s i)) (fun p q => φ (.l p q))
      (fun i z τ => φ (.u i z τ)) (fun i z τ => φ (.ut i z τ))
      (fun j z τ => φ (.v j z τ)) (fun j z τ => φ (.vt j z τ)) ↔
      ∀ k, clause I X' rt par J Ip φ k := by
  classical
  constructor
  · rintro ⟨_, _, _, _, ha, hb', hc, he, hf, hg, hi, hj⟩ k
    cases k with
    | a i z => exact ha i z
    | b i z => exact ⟨hb' i z, hc i z⟩
    | e j z => exact he j z
    | f j z => exact ⟨hf j z, hg j z⟩
    | pair z p q => exact fun hp hq hpq => hi z p hp q hq hpq
    | triple z p q x => exact fun hp hq hx h1 h2 h3 => hj z p hp q hq x hx h1 h2 h3
  · intro h
    refine ⟨fun i => hb _, fun z p _ q _ => hb _, fun i z τ => ⟨hb _, hb _⟩,
      fun j z τ => ⟨hb _, hb _⟩, fun i z => h (.a i z), fun i z => (h (.b i z)).1,
      fun i z => (h (.b i z)).2, fun j z => h (.e j z), fun j z => (h (.f j z)).1,
      fun j z => (h (.f j z)).2, fun z p hp q hq hpq => h (.pair z p q) hp hq hpq,
      fun z p hp q hq x hx h1 h2 h3 => h (.triple z p q x) hp hq hx h1 h2 h3⟩

theorem clauses_of_feas (φ : Var10 I T → ℕ)
    (h : BiLP10Feasible I X' rt par J Ip (fun i => φ (.s i)) (fun p q => φ (.l p q))
      (fun i z τ => φ (.u i z τ)) (fun i z τ => φ (.ut i z τ))
      (fun j z τ => φ (.v j z τ)) (fun j z τ => φ (.vt j z τ))) :
      ∀ k, clause I X' rt par J Ip φ k := by
  classical
  obtain ⟨_, _, _, _, ha, hb', hc, he, hf, hg, hi, hj⟩ := h
  intro k
  cases k with
  | a i z => exact ha i z
  | b i z => exact ⟨hb' i z, hc i z⟩
  | e j z => exact he j z
  | f j z => exact ⟨hf j z, hg j z⟩
  | pair z p q => exact fun hp hq hpq => hi z p hp q hq hpq
  | triple z p q x => exact fun hp hq hx h1 h2 h3 => hj z p hp q hq x hx h1 h2 h3

theorem supp_l_bag (hJ : IsPartitionData I X' J Ip) (k : Con10 I T) (p q : Fin I.n ⊕ Fin I.m)
    (h : Var10.l p q ∈ supp10 I X' rt par J Ip k) : ∃ z, p ∈ X' z ∧ q ∈ X' z := by
  classical
  cases k with
  | a i z =>
    simp only [supp10] at h
    split_ifs at h with hi
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨j, hj, he⟩ | ⟨τ, he⟩
      · cases he
        exact ⟨z, (hJ.1 i z j hj).2.2, hi⟩
      · cases he
    · simp at h
  | b i z =>
    simp only [supp10] at h
    split_ifs at h <;> simp at h
  | e j z =>
    simp only [supp10] at h
    split_ifs at h with hj
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨i, hi, he⟩ | ⟨τ, he⟩
      · cases he
        exact ⟨z, (hJ.2.2.2.1 j z i hi).2.1, hj⟩
      · cases he
    · simp at h
  | f j z =>
    simp only [supp10] at h
    split_ifs at h <;> simp at h
  | pair z p' q' =>
    simp only [supp10] at h
    split_ifs at h with hc
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> cases h
      · exact ⟨z, hc.1, hc.2.1⟩
      · exact ⟨z, hc.2.1, hc.1⟩
    · simp at h
  | triple z p' q' x' =>
    simp only [supp10] at h
    split_ifs at h with hc
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h <;> cases h
      · exact ⟨z, hc.1, hc.2.1⟩
      · exact ⟨z, hc.2.1, hc.2.2.1⟩
      · exact ⟨z, hc.2.2.1, hc.1⟩
    · simp at h

theorem clause_dep (φ φ' : Var10 I T → ℕ) (k : Con10 I T)
    (h : ∀ x ∈ supp10 I X' rt par J Ip k, φ x = φ' x) :
    clause I X' rt par J Ip φ k ↔ clause I X' rt par J Ip φ' k := by
  classical
  cases k with
  | a i z =>
    by_cases hi : Sum.inl i ∈ X' z
    · have e1 : (fun τ => φ (.u i z τ)) = (fun τ => φ' (.u i z τ)) :=
        funext fun τ => h _ (by simp [supp10, hi])
      have e2 : (∑ j ∈ J i z, I.r j i * φ (.l (Sum.inr j) (Sum.inl i))) =
          ∑ j ∈ J i z, I.r j i * φ' (.l (Sum.inr j) (Sum.inl i)) :=
        Finset.sum_congr rfl fun j hj => by rw [h _ (by simp [supp10, hi, hj])]
      simp only [clause, e1, e2]
    · simp [clause, hi]
  | b i z =>
    by_cases hi : Sum.inl i ∈ X' z
    · have e1 : (fun τ => φ (.u i z τ)) = (fun τ => φ' (.u i z τ)) :=
        funext fun τ => h _ (by simp [supp10, hi])
      have e2 : (∑ z' ∈ (children rt par z).filter (fun z' => Sum.inl i ∈ X' z'),
            bitVal (fun τ => φ (.ut i z' τ))) =
          ∑ z' ∈ (children rt par z).filter (fun z' => Sum.inl i ∈ X' z'),
            bitVal (fun τ => φ' (.ut i z' τ)) := by
        apply Finset.sum_congr rfl
        intro z' hz'
        congr 1
        funext τ
        apply h
        simp only [supp10, hi, if_true, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact Or.inl (Or.inr ⟨z', hz', τ, rfl⟩)
      by_cases hr : IsSubtreeRoot I X' rt par (Sum.inl i) z
      · have e3 : φ (.s i) = φ' (.s i) := h _ (by simp [supp10, hi, hr])
        simp only [clause, e1, e2, e3, hr, not_true_eq_false, false_implies, implies_true,
          true_and, and_true, forall_const]
      · have e3 : (fun τ => φ (.ut i z τ)) = (fun τ => φ' (.ut i z τ)) :=
          funext fun τ => h _ (by simp [supp10, hi, hr])
        simp only [clause, e1, e2, e3, hr, false_implies, and_true, not_false_eq_true,
          forall_const]
    · have hr : ¬ IsSubtreeRoot I X' rt par (Sum.inl i) z := fun h' => hi h'.1
      simp [clause, hi, hr]
  | e j z =>
    by_cases hj : Sum.inr j ∈ X' z
    · have e1 : (fun τ => φ (.v j z τ)) = (fun τ => φ' (.v j z τ)) :=
        funext fun τ => h _ (by simp [supp10, hj])
      have e2 : (∑ i ∈ Ip j z, φ (.l (Sum.inl i) (Sum.inr j))) =
          ∑ i ∈ Ip j z, φ' (.l (Sum.inl i) (Sum.inr j)) :=
        Finset.sum_congr rfl fun i hi => by rw [h _ (by simp [supp10, hj, hi])]
      simp only [clause, e1, e2]
    · simp [clause, hj]
  | f j z =>
    by_cases hj : Sum.inr j ∈ X' z
    · have e1 : (fun τ => φ (.v j z τ)) = (fun τ => φ' (.v j z τ)) :=
        funext fun τ => h _ (by simp [supp10, hj])
      have e2 : (∑ z' ∈ (children rt par z).filter (fun z' => Sum.inr j ∈ X' z'),
            bitVal (fun τ => φ (.vt j z' τ))) =
          ∑ z' ∈ (children rt par z).filter (fun z' => Sum.inr j ∈ X' z'),
            bitVal (fun τ => φ' (.vt j z' τ)) := by
        apply Finset.sum_congr rfl
        intro z' hz'
        congr 1
        funext τ
        apply h
        simp only [supp10, hj, if_true, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact Or.inl (Or.inr ⟨z', hz', τ, rfl⟩)
      by_cases hr : IsSubtreeRoot I X' rt par (Sum.inr j) z
      · simp only [clause, e1, e2, hr, not_true_eq_false, false_implies, implies_true,
          true_and, and_true, forall_const]
      · have e3 : (fun τ => φ (.vt j z τ)) = (fun τ => φ' (.vt j z τ)) :=
          funext fun τ => h _ (by simp [supp10, hj, hr])
        simp only [clause, e1, e2, e3, hr, false_implies, and_true, not_false_eq_true,
          forall_const]
    · have hr : ¬ IsSubtreeRoot I X' rt par (Sum.inr j) z := fun h' => hj h'.1
      simp [clause, hj, hr]
  | pair z p q =>
    by_cases hc : p ∈ X' z ∧ q ∈ X' z ∧ p ≠ q
    · have e1 := h (.l p q) (by simp [supp10, hc])
      have e2 := h (.l q p) (by simp [supp10, hc])
      simp only [clause, e1, e2]
    · simp only [clause]
      constructor <;> intro _ hp hq hpq <;> exact absurd ⟨hp, hq, hpq⟩ hc
  | triple z p q x =>
    by_cases hc : p ∈ X' z ∧ q ∈ X' z ∧ x ∈ X' z ∧ p ≠ q ∧ q ≠ x ∧ p ≠ x
    · have e1 := h (.l p q) (by simp [supp10, hc])
      have e2 := h (.l q x) (by simp [supp10, hc])
      have e3 := h (.l x p) (by simp [supp10, hc])
      simp only [clause, e1, e2, e3]
    · simp only [clause]
      constructor <;> intro _ hp hq hx h1 h2 h3 <;> exact absurd ⟨hp, hq, hx, h1, h2, h3⟩ hc

end

section Encode
variable (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
  (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
  (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))

/-- Declared variables: the `s_i` and every variable occurring in a constraint. -/
def Dcl (x : Var10 I T) : Prop := (∃ i, x = .s i) ∨ ∃ k, x ∈ supp10 I X' rt par J Ip k

/-- Declared variables other than the `s_i`. -/
abbrev Aux := {x : Var10 I T // Dcl I X' rt par J Ip x ∧ ∀ i, x ≠ .s i}

noncomputable def pAux : ℕ := Nat.card (Aux I X' rt par J Ip)

noncomputable def eAux : Aux I X' rt par J Ip ≃ Fin (pAux I X' rt par J Ip) := Finite.equivFin _

/-- Decoding of the coordinates: first the `s_i`, then the auxiliary variables. -/
noncomputable def dec : Fin (I.n + pAux I X' rt par J Ip) → Var10 I T :=
  Fin.addCases (fun i => Var10.s i) (fun q => ((eAux I X' rt par J Ip).symm q).1)

theorem dec_castAdd (i : Fin I.n) :
    dec I X' rt par J Ip (Fin.castAdd _ i) = Var10.s i := by
  simp [dec]

theorem dec_inj : Function.Injective (dec I X' rt par J Ip) := by
  intro a b h
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left i' => simp [dec] at h; rw [h]
    | right q' =>
      simp only [dec, Fin.addCases_left, Fin.addCases_right] at h
      exact absurd h.symm (((eAux I X' rt par J Ip).symm q').2.2 i)
  | right q =>
    induction b using Fin.addCases with
    | left i' =>
      simp only [dec, Fin.addCases_left, Fin.addCases_right] at h
      exact absurd h (((eAux I X' rt par J Ip).symm q).2.2 i')
    | right q' =>
      simp only [dec, Fin.addCases_right] at h
      have := Subtype.ext h
      rw [(eAux I X' rt par J Ip).symm.injective this]

theorem dec_surj (x : Var10 I T) (hx : Dcl I X' rt par J Ip x) :
    ∃ v, dec I X' rt par J Ip v = x := by
  classical
  by_cases hs : ∃ i, x = .s i
  · obtain ⟨i, rfl⟩ := hs
    exact ⟨Fin.castAdd _ i, dec_castAdd I X' rt par J Ip i⟩
  · push Not at hs
    refine ⟨Fin.natAdd I.n (eAux I X' rt par J Ip ⟨x, hx, hs⟩), ?_⟩
    simp [dec]

open Classical in
/-- The valuation determined by a Boolean assignment of the coordinates. -/
noncomputable def φz (z : Fin (I.n + pAux I X' rt par J Ip) → Bool) (x : Var10 I T) : ℕ :=
  if h : ∃ v, dec I X' rt par J Ip v = x then (if z h.choose then 1 else 0) else 0

theorem φz_dec (z : Fin (I.n + pAux I X' rt par J Ip) → Bool) (v : Fin (I.n + pAux I X' rt par J Ip)) :
    φz I X' rt par J Ip z (dec I X' rt par J Ip v) = if z v then 1 else 0 := by
  classical
  have h : ∃ v', dec I X' rt par J Ip v' = dec I X' rt par J Ip v := ⟨v, rfl⟩
  have hc := dec_inj I X' rt par J Ip h.choose_spec
  simp only [φz, dif_pos h, hc]

theorem φz_le (z : Fin (I.n + pAux I X' rt par J Ip) → Bool) (x : Var10 I T) :
    φz I X' rt par J Ip z x ≤ 1 := by
  classical
  unfold φz; split_ifs <;> omega

open Classical in
/-- The supports, as coordinate sets. -/
noncomputable def sp (k : Con10 I T) : Finset (Fin (I.n + pAux I X' rt par J Ip)) :=
  Finset.univ.filter (fun v => dec I X' rt par J Ip v ∈ supp10 I X' rt par J Ip k)

theorem hdep (k : Con10 I T) (z z' : Fin (I.n + pAux I X' rt par J Ip) → Bool)
    (h : ∀ u ∈ sp I X' rt par J Ip k, z u = z' u) :
    clause I X' rt par J Ip (φz I X' rt par J Ip z) k ↔
      clause I X' rt par J Ip (φz I X' rt par J Ip z') k := by
  classical
  apply clause_dep
  intro x hx
  obtain ⟨v, rfl⟩ := dec_surj I X' rt par J Ip x (Or.inr ⟨k, hx⟩)
  rw [φz_dec, φz_dec, h v (by simp [sp, hx])]

theorem tw_sp (W : ℕ)
    (hW : RobertsonSeymour1986.GM5.TreewidthLE (intersectionGraph10 I X' rt par J Ip) W) :
    RobertsonSeymour1986.GM5.TreewidthLE (intersectionGraph (sp I X' rt par J Ip)) W := by
  classical
  apply TATW.tw_comap (dec I X' rt par J Ip) (dec_inj I X' rt par J Ip) _ _ _ W hW
  intro a b hab
  obtain ⟨hne, k, ha, hb⟩ := hab
  refine ⟨fun h => hne (dec_inj I X' rt par J Ip h), k, ?_, ?_⟩
  · simpa [sp] using ha
  · simpa [sp] using hb

end Encode

section Char
variable (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
  (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
  (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))

theorem image_eq (hJ : IsPartitionData I X' J Ip)
    (char10 : ∀ s : Fin I.n → ℕ, (∃ ℓ u ut v vt, BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt) ↔
      ∃ S, FullyActivates I S ∧ ∀ i, s i = if i ∈ S then 1 else 0) :
    (fun x : Fin (I.n + pAux I X' rt par J Ip) → ℝ => fun i => x (Fin.castAdd _ i)) ''
      (TAP4.bval '' {z | ∀ k, clause I X' rt par J Ip (φz I X' rt par J Ip z) k}) =
      ind '' {S : Finset (Fin I.n) | FullyActivates I S} := by
  classical
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hfeas := (feas_iff_clauses I X' rt par J Ip (φz I X' rt par J Ip z)
      (φz_le I X' rt par J Ip z)).2 hz
    obtain ⟨S, hS, hs⟩ := (char10 _).1 ⟨_, _, _, _, _, hfeas⟩
    refine ⟨S, hS, ?_⟩
    funext i
    have := hs i
    rw [← dec_castAdd I X' rt par J Ip i, φz_dec] at this
    simp only [ind, TAP4.bval]
    by_cases hzi : z (Fin.castAdd _ i) = true <;> by_cases hiS : i ∈ S <;> simp_all
  · rintro ⟨S, hS, rfl⟩
    obtain ⟨ℓ, u, ut, v, vt, h⟩ := (char10 (fun i => if i ∈ S then 1 else 0)).2 ⟨S, hS, fun i => rfl⟩
    let ψ : Var10 I T → ℕ := fun x => match x with
      | .s i => if i ∈ S then 1 else 0
      | .l p q => ℓ p q
      | .u i z τ => u i z τ
      | .ut i z τ => ut i z τ
      | .v j z τ => v j z τ
      | .vt j z τ => vt j z τ
    have h' : BiLP10Feasible I X' rt par J Ip (fun i => ψ (.s i)) (fun p q => ψ (.l p q))
        (fun i z τ => ψ (.u i z τ)) (fun i z τ => ψ (.ut i z τ))
        (fun j z τ => ψ (.v j z τ)) (fun j z τ => ψ (.vt j z τ)) := h
    have hcl := clauses_of_feas I X' rt par J Ip ψ h'
    have hle : ∀ x, Dcl I X' rt par J Ip x → ψ x ≤ 1 := by
      intro x hx
      cases x with
      | s i => simp only [ψ]; split_ifs <;> omega
      | l p q =>
        rcases hx with ⟨i, hi⟩ | ⟨k, hk⟩
        · cases hi
        · obtain ⟨z, hp, hq⟩ := supp_l_bag I X' rt par J Ip hJ k p q hk
          exact h.2.1 z p hp q hq
      | u i z τ => exact (h.2.2.1 i z τ).1
      | ut i z τ => exact (h.2.2.1 i z τ).2
      | v j z τ => exact (h.2.2.2.1 j z τ).1
      | vt j z τ => exact (h.2.2.2.1 j z τ).2
    let z : Fin (I.n + pAux I X' rt par J Ip) → Bool := fun w =>
      decide (ψ (dec I X' rt par J Ip w) = 1)
    have hagree : ∀ x, Dcl I X' rt par J Ip x → φz I X' rt par J Ip z x = ψ x := by
      intro x hx
      obtain ⟨w, rfl⟩ := dec_surj I X' rt par J Ip x hx
      rw [φz_dec]
      have := hle _ hx
      simp only [z]
      by_cases h1 : ψ (dec I X' rt par J Ip w) = 1
      · simp [h1]
      · simp only [h1, decide_false, Bool.false_eq_true, if_false]; omega
    refine ⟨TAP4.bval z, ⟨z, ?_, rfl⟩, ?_⟩
    · intro k
      exact (clause_dep I X' rt par J Ip _ _ k
        (fun x hx => hagree x (Or.inr ⟨k, hx⟩))).2 (hcl k)
    · funext i
      simp only [TAP4.bval, ind, z, dec_castAdd, ψ]
      by_cases hiS : i ∈ S <;> simp [hiS]

end Char

theorem ef_proj {a b N K : ℕ} (A : Matrix (Fin K) (Fin (a + b) ⊕ Fin N) ℝ) (bb : Fin K → ℝ) :
    ∃ A' : Matrix (Fin K) (Fin a ⊕ Fin (b + N)) ℝ,
      {x : Fin a → ℝ | ∃ y : Fin (b + N) → ℝ, LinFeasible A' bb x y} =
        (fun x : Fin (a + b) → ℝ => fun i => x (Fin.castAdd b i)) ''
          {x | ∃ y : Fin N → ℝ, LinFeasible A bb x y} := by
  let A' : Matrix (Fin K) (Fin a ⊕ Fin (b + N)) ℝ := fun r =>
    Sum.elim (fun i => A r (Sum.inl (Fin.castAdd b i)))
      (fun j => Fin.addCases (fun q => A r (Sum.inl (Fin.natAdd a q))) (fun k => A r (Sum.inr k)) j)
  have key : ∀ r (x : Fin a → ℝ) (y' : Fin (b + N) → ℝ),
      (∑ v, A' r v * Sum.elim x y' v) =
        ∑ v, A r v * Sum.elim (Fin.addCases x (fun q => y' (Fin.castAdd N q)))
          (fun k => y' (Fin.natAdd b k)) v := by
    intro r x y'
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_add, A',
      Fin.addCases_left, Fin.addCases_right]
    ring
  refine ⟨A', ?_⟩
  ext x
  constructor
  · rintro ⟨y', hy'⟩
    refine ⟨Fin.addCases x (fun q => y' (Fin.castAdd N q)), ⟨fun k => y' (Fin.natAdd b k), ?_⟩, ?_⟩
    · intro r
      have := hy' r
      rw [key] at this
      exact this
    · funext i; simp
  · rintro ⟨X, ⟨Y, hY⟩, rfl⟩
    refine ⟨Fin.addCases (fun q => X (Fin.natAdd a q)) Y, ?_⟩
    intro r
    rw [key]
    have hX : Fin.addCases (fun i => X (Fin.castAdd b i))
        (fun q => (Fin.addCases (fun q => X (Fin.natAdd a q)) Y : Fin (b + N) → ℝ)
          (Fin.castAdd N q)) = X := by
      funext u
      induction u using Fin.addCases <;> simp
    have hY' : (fun k => (Fin.addCases (fun q => X (Fin.natAdd a q)) Y : Fin (b + N) → ℝ)
        (Fin.natAdd b k)) = Y := by
      funext k; simp
    rw [hX, hY']
    exact hY r

theorem pAux_le (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
    (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n)) (ω' : ℕ)
    (hJ : IsPartitionData I X' J Ip)
    (hbin : ∀ z, (Finset.univ.filter (fun z' => z' ≠ rt ∧ par z' = z)).card ≤ 2)
    (hω : ∀ z, (X' z).card ≤ ω' + 1) :
    pAux I X' rt par J Ip ≤ Fintype.card T *
      (9 * (ω' + 1) ^ 2 + 9 * (ω' + 1) * (Nat.log 2 (varthetaMax I) + 1) + 1) := by
  classical
  let S : Finset (Var10 I T) := Finset.univ.biUnion (fun z => Finset.univ.filter (inBag I X' rt par z))
  have hS : S.card ≤ Fintype.card T *
      (9 * (ω' + 1) ^ 2 + 9 * (ω' + 1) * (Nat.log 2 (varthetaMax I) + 1) + 1) := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ (fun z _ => inBag_card I X' rt par ω' hbin hω z)) ?_
    simp
  refine le_trans ?_ hS
  unfold pAux
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_le_card_of_injective (fun x : Aux I X' rt par J Ip => (⟨x.1, ?_⟩ : {x // x ∈ S}))
  · intro a b h
    have := congrArg Subtype.val h
    simp only at this
    exact Subtype.ext this
  · obtain ⟨hd, hns⟩ := x.2
    rcases hd with ⟨i, hi⟩ | ⟨k, hk⟩
    · exact absurd hi (hns i)
    · obtain ⟨z, hz⟩ := supp_inBag I X' rt par J Ip hJ k
      simp only [S, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨z, hz _ hk⟩

end TAEnc


namespace TAFinal

open TraceAdopt.LPReform

theorem size_bound (n m a L ϑ p N1 K : ℕ) (ha : 1 ≤ a) (hL : 2 ^ L ≤ ϑ + 1)
    (hp : p ≤ (2 * (n + m) + 1) * (9 * (a + 1) ^ 2 + 9 * (a + 1) * (L + 1) + 1))
    (hs : (n + p) + N1 + K ≤ 13 * 2 ^ (9 * (a + 1) ^ 2 + 9 * (a + 1) * (L + 1)) * (n + p + 1)) :
    n + (p + N1) + K ≤ 2 ^ (108 * a ^ 2) * (ϑ + 1) ^ (108 * a) * (108 * (n + m + 1)) := by
  set W := 9 * (a + 1) ^ 2 + 9 * (a + 1) * (L + 1) with hW
  have h1 : n + p + 1 ≤ 3 * (n + m + 1) * (W + 1) := by
    have : (2 * (n + m) + 1) * (W + 1) ≤ 2 * (n + m + 1) * (W + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have h2 : W + 1 ≤ 2 ^ W := Nat.lt_two_pow_self
  have h3 : n + (p + N1) + K ≤ 39 * (n + m + 1) * (2 ^ W * 2 ^ W) := by
    have := Nat.mul_le_mul_left (13 * 2 ^ W) h1
    have h4 : 13 * 2 ^ W * (3 * (n + m + 1) * (W + 1)) ≤ 13 * 2 ^ W * (3 * (n + m + 1) * 2 ^ W) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    calc n + (p + N1) + K = (n + p) + N1 + K := by ring
      _ ≤ 13 * 2 ^ W * (n + p + 1) := hs
      _ ≤ 13 * 2 ^ W * (3 * (n + m + 1) * (W + 1)) := this
      _ ≤ 13 * 2 ^ W * (3 * (n + m + 1) * 2 ^ W) := h4
      _ = 39 * (n + m + 1) * (2 ^ W * 2 ^ W) := by ring
  -- bound `2 ^ W`
  have h5 : 2 ^ (9 * (a + 1) ^ 2) ≤ 2 ^ (36 * a ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h6 : 2 ^ (9 * (a + 1) * (L + 1)) ≤ 2 ^ (18 * a ^ 2) * (ϑ + 1) ^ (18 * a) := by
    have e : 2 ^ (9 * (a + 1) * (L + 1)) = (2 ^ (L + 1)) ^ (9 * (a + 1)) := by
      rw [← pow_mul]; ring_nf
    rw [e]
    have hb : 2 ^ (L + 1) ≤ 2 * (ϑ + 1) := by rw [pow_succ]; omega
    calc (2 ^ (L + 1)) ^ (9 * (a + 1)) ≤ (2 * (ϑ + 1)) ^ (9 * (a + 1)) :=
          Nat.pow_le_pow_left hb _
      _ = 2 ^ (9 * (a + 1)) * (ϑ + 1) ^ (9 * (a + 1)) := by rw [mul_pow]
      _ ≤ 2 ^ (18 * a ^ 2) * (ϑ + 1) ^ (18 * a) := by
          apply Nat.mul_le_mul
          · exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
          · exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  have h7 : 2 ^ W ≤ 2 ^ (54 * a ^ 2) * (ϑ + 1) ^ (18 * a) := by
    rw [hW, pow_add]
    calc 2 ^ (9 * (a + 1) ^ 2) * 2 ^ (9 * (a + 1) * (L + 1))
        ≤ 2 ^ (36 * a ^ 2) * (2 ^ (18 * a ^ 2) * (ϑ + 1) ^ (18 * a)) := Nat.mul_le_mul h5 h6
      _ = 2 ^ (54 * a ^ 2) * (ϑ + 1) ^ (18 * a) := by rw [← mul_assoc, ← pow_add]; ring_nf
  have h8 : 2 ^ W * 2 ^ W ≤ 2 ^ (108 * a ^ 2) * (ϑ + 1) ^ (36 * a) := by
    calc 2 ^ W * 2 ^ W ≤ (2 ^ (54 * a ^ 2) * (ϑ + 1) ^ (18 * a)) *
        (2 ^ (54 * a ^ 2) * (ϑ + 1) ^ (18 * a)) := Nat.mul_le_mul h7 h7
      _ = 2 ^ (108 * a ^ 2) * (ϑ + 1) ^ (36 * a) := by ring
  have h9 : (ϑ + 1) ^ (36 * a) ≤ (ϑ + 1) ^ (108 * a) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc n + (p + N1) + K ≤ 39 * (n + m + 1) * (2 ^ W * 2 ^ W) := h3
    _ ≤ 39 * (n + m + 1) * (2 ^ (108 * a ^ 2) * (ϑ + 1) ^ (108 * a)) :=
        Nat.mul_le_mul_left _ (le_trans h8 (Nat.mul_le_mul_left _ h9))
    _ ≤ 108 * (n + m + 1) * (2 ^ (108 * a ^ 2) * (ϑ + 1) ^ (108 * a)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    _ = 2 ^ (108 * a ^ 2) * (ϑ + 1) ^ (108 * a) * (108 * (n + m + 1)) := by ring

theorem ta_theorem_2 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (I : Instance), I.Standing → ∀ ω : ℕ, HypTreewidthLE I ω →
        ∃ (N K : ℕ) (A : Matrix (Fin K) (Fin I.n ⊕ Fin N) ℝ)
          (b : Fin K → ℝ),
          I.n + N + K ≤
            2 ^ (C * (ω + 1) ^ 2) *
              (varthetaMax I + 1) ^ (C * (ω + 1)) *
              (C * (I.n + I.m + 1)) ∧
          {x : Fin I.n → ℝ | ∃ y : Fin N → ℝ, LinFeasible A b x y} =
            convexHull ℝ (ind '' {S : Finset (Fin I.n) | FullyActivates I S}) ∧
          ∀ w : Fin I.n → ℝ,
            IsLeast {v : ℝ | ∃ x y, LinFeasible A b x y ∧
              v = ∑ i, w i * x i} (OPT I w) := by
  refine ⟨108, by norm_num, ?_⟩
  intro I hI ω hω
  classical
  have hTW := proposition_3 I hI ω hω
  obtain ⟨T, hT, hDT, t, X', rt, par, J, Ip, hX, hJ, hwid, hcard⟩ :=
    TABin.binTD_exists I (ω + 1) hTW
  have char10 : ∀ s : Fin I.n → ℕ,
      (∃ ℓ u ut v vt, BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt) ↔
        ∃ S, FullyActivates I S ∧ ∀ i, s i = if i ∈ S then 1 else 0 := by
    intro s
    rw [(proposition_8 I hI t X' rt par J Ip hX hJ).1 s, (proposition_7 I hI t X' hX.1).1 s,
      (proposition_5 I hI).1 s]
  have hTW10 := ta_prop9 I t X' rt par J Ip (ω + 1) hX hJ hwid
  have hsp := TAEnc.tw_sp I X' rt par J Ip _ hTW10
  obtain ⟨N1, K, A, bb, hsize, heq⟩ := TAP4.ef_local
    (fun k z => TAEnc.clause I X' rt par J Ip (TAEnc.φz I X' rt par J Ip z) k)
    (TAEnc.sp I X' rt par J Ip) (TAEnc.hdep I X' rt par J Ip) _ hsp
  obtain ⟨A', hA'⟩ := TAEnc.ef_proj A bb
  have hE : {x : Fin I.n → ℝ | ∃ y, LinFeasible A' bb x y} =
      convexHull ℝ (ind '' {S : Finset (Fin I.n) | FullyActivates I S}) := by
    rw [hA', heq, ← TAEnc.image_eq I X' rt par J Ip hJ char10]
    exact LinearMap.image_convexHull
      (LinearMap.funLeft ℝ ℝ (Fin.castAdd (TAEnc.pAux I X' rt par J Ip))) _
  refine ⟨TAEnc.pAux I X' rt par J Ip + N1, K, A', bb, ?_, hE, ?_⟩
  · have hp := TAEnc.pAux_le I X' rt par J Ip (ω + 1) hJ hX.2.2.2.2 hwid
    rw [hcard] at hp
    have hL : 2 ^ Nat.log 2 (varthetaMax I) ≤ varthetaMax I + 1 := by
      by_cases h0 : varthetaMax I = 0
      · rw [h0]; simp
      · exact le_trans (Nat.pow_log_le_self 2 h0) (Nat.le_succ _)
    exact TAFinal.size_bound I.n I.m (ω + 1) (Nat.log 2 (varthetaMax I)) (varthetaMax I)
      (TAEnc.pAux I X' rt par J Ip) N1 K (by omega) hL hp hsize
  · intro w
    have hlin : IsLinearMap ℝ (fun x : Fin I.n → ℝ => ∑ i, w i * x i) := by
      constructor
      · intro x y; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      · intro c x; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
    have hind : ∀ S : Finset (Fin I.n), (∑ i, w i * ind S i) = ∑ i ∈ S, w i := by
      intro S
      simp only [ind, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hOPTle : ∀ S, FullyActivates I S → OPT I w ≤ ∑ i ∈ S, w i := by
      intro S hS
      unfold OPT
      apply Finset.inf'_le
      simpa using hS
    constructor
    · have hne : (Finset.univ.filter (FullyActivates I)).Nonempty :=
        ⟨Finset.univ, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨0, rfl⟩⟩
      obtain ⟨S0, hS0, hval⟩ := Finset.exists_mem_eq_inf' hne (fun S => ∑ i ∈ S, w i)
      have hS0' : FullyActivates I S0 := by simpa using hS0
      have hx : ind S0 ∈ {x : Fin I.n → ℝ | ∃ y, LinFeasible A' bb x y} := by
        rw [hE]; exact subset_convexHull ℝ _ ⟨S0, hS0', rfl⟩
      obtain ⟨y, hy⟩ := hx
      refine ⟨ind S0, y, hy, ?_⟩
      rw [hind]
      apply le_antisymm (hOPTle S0 hS0')
      unfold OPT
      rw [hval]
    · rintro v ⟨x, y, hy, rfl⟩
      have hx : x ∈ convexHull ℝ (ind '' {S : Finset (Fin I.n) | FullyActivates I S}) := by
        rw [← hE]; exact ⟨y, hy⟩
      have hsub : ind '' {S : Finset (Fin I.n) | FullyActivates I S} ⊆
          {x : Fin I.n → ℝ | OPT I w ≤ ∑ i, w i * x i} := by
        rintro _ ⟨S, hS, rfl⟩
        simp only [Set.mem_setOf_eq]
        rw [hind]
        exact hOPTle S hS
      exact convexHull_min hsub (convex_halfSpace_ge hlin _) hx

end TAFinal


open TraceAdopt.LPReform in
theorem solution :
    ∃ C : ℕ, 0 < C ∧
      ∀ (I : Instance), I.Standing → ∀ ω : ℕ, HypTreewidthLE I ω →
        ∃ (N K : ℕ) (A : Matrix (Fin K) (Fin I.n ⊕ Fin N) ℝ)
          (b : Fin K → ℝ),
          I.n + N + K ≤
            2 ^ (C * (ω + 1) ^ 2) *
              (varthetaMax I + 1) ^ (C * (ω + 1)) *
              (C * (I.n + I.m + 1)) ∧
          {x : Fin I.n → ℝ | ∃ y : Fin N → ℝ, LinFeasible A b x y} =
            convexHull ℝ (ind '' {S : Finset (Fin I.n) | FullyActivates I S}) ∧
          ∀ w : Fin I.n → ℝ,
            IsLeast {v : ℝ | ∃ x y, LinFeasible A b x y ∧
              v = ∑ i, w i * x i} (OPT I w) :=
  TAFinal.ta_theorem_2
