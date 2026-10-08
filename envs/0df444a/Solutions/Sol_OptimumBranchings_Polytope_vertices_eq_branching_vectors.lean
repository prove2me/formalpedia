-- Prove2me | solution 1 for OptimumBranchings.Polytope.vertices_eq_branching_vectors
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T05:09:35.145984+00:00
-- url     : https://prove2.me/submissions/5d3a8ae1-b1f3-4953-84e8-94db309dbafb

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron

set_option autoImplicit false

/- Complete checked body: RootedBasics -/
section

namespace OptimumBranchings.Polytope.Proof

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A rooted spanning tree, certified by one incoming edge and a decreasing rank. -/
structure RootedTree (G : Graph V E) (r : V) where
  edge : {v : V // v ≠ r} → E
  head : ∀ v, G.front (edge v) = v
  rank : V → ℕ
  decreasing : ∀ v, rank (G.rear (edge v)) < rank v

namespace RootedTree

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem edge_injective {G : Graph V E} {r : V} (T : RootedTree G r) :
    Function.Injective T.edge := by
  intro v w h
  apply Subtype.ext
  rw [← T.head v, ← T.head w, h]

def edges {G : Graph V E} {r : V} (T : RootedTree G r) : Finset E :=
  Finset.univ.image T.edge

def cost {G : Graph V E} {r : V} (T : RootedTree G r) (c : E → ℝ) : ℝ :=
  ∑ v, c (T.edge v)

omit [Fintype E] in
theorem sum_edges {G : Graph V E} {r : V} (T : RootedTree G r) (f : E → ℝ) :
    ∑ e ∈ T.edges, f e = ∑ v, f (T.edge v) := by
  exact Finset.sum_image (fun v _ w _ h => T.edge_injective h)

end RootedTree

def inCut (G : Graph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (fun e => G.front e ∈ S ∧ G.rear e ∉ S)

def CutFeasible (G : Graph V E) (r : V) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧
  ∀ S : Finset V, S.Nonempty → r ∉ S → 1 ≤ ∑ e ∈ inCut G S, x e

omit [Fintype V] [DecidableEq E] in
theorem inCut_singleton (G : Graph V E) (v : V) :
    inCut G {v} = Finset.univ.filter (fun e => G.front e = v) := by
  ext e
  simp only [inCut, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun h' => G.front_ne_rear e (h.trans h'.symm)⟩

omit [Fintype V] [DecidableEq E] in
theorem CutFeasible.incoming {G : Graph V E} {r : V} {x : E → ℝ}
    (hx : CutFeasible G r x) (v : V) (hv : v ≠ r) :
    1 ≤ ∑ e ∈ Finset.univ.filter (fun e => G.front e = v), x e := by
  simpa only [inCut_singleton] using
    hx.2 {v} (Finset.singleton_nonempty v) (by simpa using hv.symm)

omit [Fintype V] [DecidableEq E] in
theorem CutFeasible.incoming_nonempty {G : Graph V E} {r : V} {x : E → ℝ}
    (hx : CutFeasible G r x) (v : V) (hv : v ≠ r) :
    (Finset.univ.filter (fun e => G.front e = v)).Nonempty := by
  by_contra h
  have hz := Finset.not_nonempty_iff_eq_empty.mp h
  have hi := hx.incoming v hv
  rw [hz, Finset.sum_empty] at hi
  norm_num at hi

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: CostNormalization -/
section

namespace OptimumBranchings.Polytope.Proof

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [DecidableEq E] in
theorem minimum_incoming {G : Graph V E} {r : V} {x : E → ℝ}
    (hx : CutFeasible G r x) (c : E → ℝ) :
    ∃ pick : {v : V // v ≠ r} → E,
      (∀ v, G.front (pick v) = v) ∧
      ∀ (v : {v : V // v ≠ r}) e, G.front e = v → c (pick v) ≤ c e := by
  have h : ∀ v : {v : V // v ≠ r}, ∃ e : E,
      G.front e = v ∧ ∀ f : E, G.front f = v → c e ≤ c f := by
    intro v
    obtain ⟨e, he, hm⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun e => G.front e = v)) c (hx.incoming_nonempty v v.property)
    exact ⟨e, (Finset.mem_filter.mp he).2, fun f hf => hm f (by simpa using hf)⟩
  choose pick hp hm using h
  exact ⟨pick, hp, hm⟩

def nodePrice (r : V) (c : E → ℝ) (pick : {v : V // v ≠ r} → E) (v : V) : ℝ :=
  if hv : v = r then 0 else c (pick ⟨v, hv⟩)

def residualCost (G : Graph V E) (r : V) (c : E → ℝ)
    (pick : {v : V // v ≠ r} → E) (e : E) : ℝ :=
  c e - nodePrice r c pick (G.front e)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem residual_nonneg (G : Graph V E) (r : V) (c : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (pick : {v : V // v ≠ r} → E)
    (hmin : ∀ (v : {v : V // v ≠ r}) e, G.front e = v → c (pick v) ≤ c e) :
    ∀ e, 0 ≤ residualCost G r c pick e := by
  intro e
  unfold residualCost nodePrice
  split_ifs with he
  · simpa using hc e
  · exact sub_nonneg.mpr (hmin ⟨G.front e, he⟩ e rfl)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem residual_pick (G : Graph V E) (r : V) (c : E → ℝ)
    (pick : {v : V // v ≠ r} → E) (hhead : ∀ v, G.front (pick v) = v)
    (v : {v : V // v ≠ r}) : residualCost G r c pick (pick v) = 0 := by
  simp only [residualCost, hhead, nodePrice, v.property, dite_false, sub_self]

omit [DecidableEq E] in
theorem weighted_head_sum (G : Graph V E) (a : V → ℝ) (x : E → ℝ) :
    ∑ e, a (G.front e) * x e =
      ∑ v, a v * ∑ e ∈ Finset.univ.filter (fun e => G.front e = v), x e := by
  rw [← Finset.sum_fiberwise Finset.univ G.front (fun e => a (G.front e) * x e)]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [(Finset.mem_filter.mp he).2]

omit [DecidableEq E] in
theorem normalized_cost_lower {G : Graph V E} {r : V} {x : E → ℝ}
    (hx : CutFeasible G r x) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (pick : {v : V // v ≠ r} → E) :
    (∑ v : {v : V // v ≠ r}, c (pick v)) +
        ∑ e, residualCost G r c pick e * x e ≤ ∑ e, c e * x e := by
  let a := nodePrice r c pick
  have ha : ∀ v, 0 ≤ a v := by
    intro v
    dsimp [a, nodePrice]
    split_ifs
    · exact le_rfl
    · exact hc _
  have hnode : ∑ v, a v ≤ ∑ e, a (G.front e) * x e := by
    rw [weighted_head_sum]
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v = r
    · subst v
      simp [a, nodePrice]
    · exact le_mul_of_one_le_right (ha v) (hx.incoming v hv)
  have hsum : ∑ v, a v = ∑ v : {v : V // v ≠ r}, c (pick v) := by
    calc
      _ = ∑ v ∈ Finset.univ.filter (fun v : V => v ≠ r), a v := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v = r <;> simp [a, nodePrice, hv]
      _ = ∑ v : {v : V // v ≠ r}, a v :=
        Finset.sum_subtype _ (by intro v; simp) a
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        simp [a, nodePrice, v.property]
  rw [hsum] at hnode
  have heq : ∑ e, c e * x e =
      (∑ e, a (G.front e) * x e) + ∑ e, residualCost G r c pick e * x e := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    dsimp [residualCost, a]
    ring
  rw [heq]
  exact add_le_add hnode le_rfl

omit [Fintype E] [DecidableEq E] in
theorem tree_cost_normalized (G : Graph V E) (r : V) (c : E → ℝ)
    (pick : {v : V // v ≠ r} → E) (T : RootedTree G r) :
    T.cost c = (∑ v : {v : V // v ≠ r}, c (pick v)) +
      T.cost (residualCost G r c pick) := by
  unfold RootedTree.cost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [residualCost, T.head, nodePrice, v.property, dite_false]
  ring

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: CycleQuotient -/
section

namespace OptimumBranchings.Polytope.Proof

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev ContractV (C : Finset V) := Option {v : V // v ∉ C}

def contract (C : Finset V) (v : V) : ContractV C :=
  if hv : v ∈ C then none else some ⟨v, hv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_none_iff (C : Finset V) (v : V) : contract C v = none ↔ v ∈ C := by
  simp [contract]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_some (C : Finset V) (v : {v : V // v ∉ C}) :
    contract C v = some v := by
  simp [contract, v.property]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_eq_some_iff (C : Finset V) (v : V) (w : {v : V // v ∉ C}) :
    contract C v = some w ↔ v = w := by
  by_cases hv : v ∈ C
  · have hn : v ≠ w := fun h => w.property (h ▸ hv)
    simp [contract, hv, hn]
  · simp only [contract, hv, dite_false, Option.some.injEq]
    exact Subtype.ext_iff

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contract_surjective (C : Finset V) (hC : C.Nonempty) :
    Function.Surjective (contract C) := by
  intro q
  cases q with
  | none =>
    obtain ⟨v, hv⟩ := hC
    exact ⟨v, (contract_none_iff C v).mpr hv⟩
  | some v => exact ⟨v, contract_some C v⟩

abbrev ContractE (G : Graph V E) (C : Finset V) :=
  {e : E // contract C (G.front e) ≠ contract C (G.rear e)}

def contractGraph (G : Graph V E) (C : Finset V) : Graph (ContractV C) (ContractE G C) where
  front e := contract C (G.front e)
  rear e := contract C (G.rear e)
  front_ne_rear e := e.property

def contractRoot (C : Finset V) (r : V) (hr : r ∉ C) : ContractV C := some ⟨r, hr⟩

theorem contract_card_lt (C : Finset V) (hC : 2 ≤ C.card) :
    Fintype.card (ContractV C) < Fintype.card V := by
  have hsplit := Finset.card_add_card_compl C
  have hc : Fintype.card {v : V // v ∉ C} = Cᶜ.card := by
    simpa only [Finset.mem_compl] using (Fintype.card_coe Cᶜ)
  simp only [Fintype.card_option, hc]
  omega

omit [DecidableEq E] in
theorem contract_cut_sum (G : Graph V E) (C : Finset V) (x : E → ℝ)
    (S : Finset (ContractV C)) :
    ∑ e ∈ inCut (contractGraph G C) S, x e.val =
      ∑ e ∈ inCut G (Finset.univ.filter (fun v => contract C v ∈ S)), x e := by
  classical
  simp only [inCut]
  rw [Finset.sum_filter, Finset.sum_filter]
  change (∑ e : ContractE G C,
    if contract C (G.front e.val) ∈ S ∧ contract C (G.rear e.val) ∉ S then x e.val else 0) = _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun e : E => contract C (G.front e) ≠ contract C (G.rear e)))
    (by intro e; simp)
    (fun e => if contract C (G.front e) ∈ S ∧ contract C (G.rear e) ∉ S then x e else 0)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : contract C (G.front e) = contract C (G.rear e)
  · simp [h]
  · simp [h]

omit [DecidableEq E] in
theorem contract_feasible (G : Graph V E) (C : Finset V) (hC : C.Nonempty)
    (r : V) (hr : r ∉ C) (x : E → ℝ) (hx : CutFeasible G r x) :
    CutFeasible (contractGraph G C) (contractRoot C r hr) (fun e => x e.val) := by
  refine ⟨fun e => hx.1 e, ?_⟩
  intro S hS hrS
  rw [contract_cut_sum]
  apply hx.2
  · obtain ⟨q, hq⟩ := hS
    obtain ⟨v, hv⟩ := contract_surjective C hC q
    exact ⟨v, by simp [hv, hq]⟩
  · intro hm
    have hc := (Finset.mem_filter.mp hm).2
    rw [contract_some C ⟨r, hr⟩] at hc
    exact hrS hc

omit [Fintype V] [DecidableEq E] in
theorem contract_cost_le (G : Graph V E) (C : Finset V) (c x : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hx : ∀ e, 0 ≤ x e) :
    (∑ e : ContractE G C, c e.val * x e.val) ≤ ∑ e, c e * x e := by
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun e : E => contract C (G.front e) ≠ contract C (G.rear e)))
    (by intro e; simp) (fun e => c e * x e)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro e _ _
  exact mul_nonneg (hc e) (hx e)

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: ParentCycles -/
section

namespace OptimumBranchings.Polytope.Proof

open scoped Classical

variable {V : Type*}

/-- A finite single orbit closed under a parent map. -/
structure ParentCycle (p : V → V) where
  support : Finset V
  nonempty : support.Nonempty
  maps : ∀ v ∈ support, p v ∈ support
  reaches : ∀ u ∈ support, ∀ v ∈ support, ∃ k : ℕ, p^[k] u = v

noncomputable def hitRank (p : V → V) (r v : V) : ℕ :=
  if h : ∃ k : ℕ, p^[k] v = r then Nat.find h else 0

theorem hitRank_decreases (p : V → V) (r v : V)
    (h : ∃ k : ℕ, p^[k] v = r) (hv : v ≠ r) :
    hitRank p r (p v) < hitRank p r v := by
  have hn : Nat.find h ≠ 0 := by
    intro he
    have hs := Nat.find_spec h
    rw [he] at hs
    exact hv hs
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hs : p^[k] (p v) = r := by
    have hs := Nat.find_spec h
    rw [hk,Function.iterate_succ_apply] at hs
    exact hs
  have hp : ∃ j : ℕ, p^[j] (p v) = r := ⟨k,hs⟩
  simp only [hitRank,dif_pos h,dif_pos hp]
  rw [hk]
  exact Nat.lt_succ_of_le (Nat.find_min' hp hs)

theorem exists_parent_cycle (p : V → V) (U : Finset V) (hne : U.Nonempty)
    (hclosed : ∀ v ∈ U, p v ∈ U) :
    ∃ C : ParentCycle p, C.support ⊆ U := by
  let F := U.powerset.filter (fun C => C.Nonempty ∧ ∀ v ∈ C, p v ∈ C)
  have hF : F.Nonempty := ⟨U,Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (fun _ h => h),hne,hclosed⟩⟩
  obtain ⟨C,hCF,hmin⟩ := Finset.exists_min_image F Finset.card hF
  obtain ⟨hsub,hneC,hclosedC⟩ : C ⊆ U ∧ C.Nonempty ∧ ∀ v ∈ C,p v ∈ C := by
    simpa [F] using hCF
  refine ⟨⟨C,hneC,hclosedC,?_⟩,hsub⟩
  intro u hu v hv
  let O := C.filter (fun w => ∃ k : ℕ,p^[k] u=w)
  have hOC : O ⊆ C := Finset.filter_subset _ _
  have hO : O.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,⟨0,rfl⟩⟩⟩
  have hclosedO : ∀ w ∈ O,p w ∈ O := by
    intro w hw
    obtain ⟨hwC,k,hk⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨hclosedC w hwC,k+1,?_⟩
    rw [Function.iterate_succ_apply',hk]
  have hOF : O ∈ F := by
    simp only [F,Finset.mem_filter,Finset.mem_powerset]
    exact ⟨hOC.trans hsub,hO,hclosedO⟩
  have heq : O=C := Finset.eq_of_subset_of_card_le hOC (hmin O hOF)
  have hvO : v ∈ O := heq.symm ▸ hv
  exact (Finset.mem_filter.mp hvO).2

namespace ParentCycle

variable {p : V → V}

theorem iterate_mem (C : ParentCycle p) {v : V} (hv : v ∈ C.support) (k : ℕ) :
    p^[k] v ∈ C.support := by
  induction k with
  | zero => exact hv
  | succ k ih => rw [Function.iterate_succ_apply']; exact C.maps _ ih

theorem surjOn (C : ParentCycle p) : Set.SurjOn p C.support C.support := by
  intro v hv
  obtain ⟨k,hk⟩ := C.reaches (p v) (C.maps v hv) v hv
  refine ⟨p^[k] v,C.iterate_mem hv k,?_⟩
  rw [←Function.iterate_succ_apply' p k v,Function.iterate_succ_apply p k v]
  exact hk

theorem injOn (C : ParentCycle p) : Set.InjOn p C.support := by
  let f : C.support → C.support := fun v => ⟨p v,C.maps v v.2⟩
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨u,hu,he⟩ := C.surjOn v.2
    exact ⟨⟨u,hu⟩,Subtype.ext he⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hf
  intro u hu v hv he
  have h := hinj (show f ⟨u,hu⟩=f ⟨v,hv⟩ from Subtype.ext he)
  exact congrArg Subtype.val h

theorem card_ge_two (C : ParentCycle p) (h : ∀ v ∈ C.support,p v ≠ v) :
    2 ≤ C.support.card := by
  obtain ⟨v,hv⟩ := C.nonempty
  have hc : 1 < C.support.card := Finset.one_lt_card.mpr
    ⟨v,hv,p v,C.maps v hv,(h v hv).symm⟩
  exact hc

theorem rank_parent_lt (C : ParentCycle p) (e : V) (he : e ∈ C.support)
    (v : V) (hv : v ∈ C.support) (hne : v ≠ e) :
    hitRank p e (p v) < hitRank p e v :=
  hitRank_decreases p e v (C.reaches v hv e he) hne

theorem rank_bounded (C : ParentCycle p) (e : V) :
    ∃ K : ℕ, ∀ v ∈ C.support, hitRank p e v < K := by
  refine ⟨(∑ v ∈ C.support,hitRank p e v)+1,?_⟩
  intro v hv
  exact Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv)

end ParentCycle

theorem parent_dichotomy [Fintype V] (p : V → V) (r : V) :
    (∃ rank : V → ℕ, ∀ v, v ≠ r → rank (p v) < rank v) ∨
      ∃ C : ParentCycle p, r ∉ C.support := by
  by_cases h : ∀ v : V,∃ k : ℕ,p^[k] v=r
  · exact Or.inl ⟨hitRank p r,fun v hv => hitRank_decreases p r v (h v) hv⟩
  · obtain ⟨v,hv⟩ := not_forall.mp h
    let U := Finset.univ.filter (fun w => ¬∃ k : ℕ,p^[k] w=r)
    have hU : U.Nonempty := ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩
    have hc : ∀ w ∈ U,p w ∈ U := by
      intro w hw
      have hn := (Finset.mem_filter.mp hw).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rintro ⟨k,hk⟩
      apply hn
      refine ⟨k+1,?_⟩
      rw [Function.iterate_succ_apply]
      exact hk
    obtain ⟨C,hC⟩ := exists_parent_cycle p U hU hc
    refine Or.inr ⟨C,?_⟩
    intro hr
    have hn := (Finset.mem_filter.mp (hC hr)).2
    exact hn ⟨0,rfl⟩

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: TreeLift -/
section

namespace OptimumBranchings.Polytope.Proof

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

private theorem scaled_rank_lt (K a b u v : ℕ) (hab : a < b) (hu : u < K) :
    K * a + u < K * b + v := by
  have h := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hab)
  nlinarith

omit [Fintype E] [DecidableEq E] in
theorem lift_rooted_tree (G : Graph V E) (r : V)
    (pick : {v : V // v ≠ r} → E) (hhead : ∀ v, G.front (pick v) = v)
    (p : V → V) (hparent : ∀ v, G.rear (pick v) = p v)
    (C : ParentCycle p) (hr : r ∉ C.support) (c : E → ℝ)
    (hzero : ∀ v, c (pick v) = 0)
    (T : RootedTree (contractGraph G C.support) (contractRoot C.support r hr)) :
    ∃ U : RootedTree G r, U.cost c = T.cost (fun e => c e.val) := by
  classical
  let qr := contractRoot C.support r hr
  let q0 : {q : ContractV C.support // q ≠ qr} := ⟨none, by simp [qr, contractRoot]⟩
  let e0 : E := (T.edge q0).val
  let entry := G.front e0
  have hentry : entry ∈ C.support := by
    apply (contract_none_iff C.support entry).mp
    exact T.head q0
  have hentryr : entry ≠ r := fun h => hr (h ▸ hentry)
  let outside (v : {v : V // v ≠ r}) (hv : v.val ∉ C.support) :
      {q : ContractV C.support // q ≠ qr} :=
    ⟨some ⟨v, hv⟩, by
      intro h
      have he : (v : V) = r := congrArg (fun q : ContractV C.support =>
        q.elim r Subtype.val) h
      exact v.property he⟩
  let edge (v : {v : V // v ≠ r}) : E :=
    if hv : v.val ∈ C.support then (if v.val = entry then e0 else pick v)
    else (T.edge (outside v hv)).val
  have hedge : ∀ v, G.front (edge v) = v := by
    intro v
    dsimp [edge]
    split_ifs with hv he
    · exact he.symm
    · exact hhead v
    · exact (contract_eq_some_iff C.support _ ⟨v, hv⟩).mp (T.head (outside v hv))
  obtain ⟨K, hK⟩ := C.rank_bounded entry
  have hK0 : 0 < K := lt_of_le_of_lt (Nat.zero_le _) (hK entry hentry)
  let off (v : V) := if v ∈ C.support then hitRank p entry v else 0
  have hoff : ∀ v, off v < K := by
    intro v
    dsimp [off]
    split_ifs with hv
    · exact hK v hv
    · exact hK0
  let rank (v : V) := K * T.rank (contract C.support v) + off v
  have hdec : ∀ v, rank (G.rear (edge v)) < rank v := by
    intro v
    by_cases hv : v.val ∈ C.support
    · by_cases he : v.val = entry
      · have heq : edge v = e0 := by simp only [edge, dif_pos hv, if_pos he]
        have hq := T.decreasing q0
        have hfront : contract C.support v = none := (contract_none_iff _ _).mpr hv
        dsimp [contractGraph, q0, e0] at hq
        rw [heq]
        dsimp [rank]
        rw [hfront]
        exact scaled_rank_lt K _ _ _ _ hq (hoff _)
      · have heq : edge v = pick v := by simp [edge, hv, he]
        have hpv := C.maps v hv
        have hc1 : contract C.support v = none := (contract_none_iff _ _).mpr hv
        have hc2 : contract C.support (p v) = none := (contract_none_iff _ _).mpr hpv
        rw [heq, hparent]
        dsimp [rank]
        rw [hc1, hc2]
        simp only [off, hv, hpv, if_pos]
        exact Nat.add_lt_add_left (C.rank_parent_lt entry hentry v hv he) _
    · have heq : edge v = (T.edge (outside v hv)).val := by simp [edge, hv]
      have hq := T.decreasing (outside v hv)
      change T.rank (contract C.support (G.rear (T.edge (outside v hv)).val)) <
        T.rank (some ⟨v.val, hv⟩) at hq
      rw [heq]
      dsimp [rank]
      rw [contract_some C.support ⟨v, hv⟩]
      exact scaled_rank_lt K _ _ _ _ hq (hoff _)
  let U : RootedTree G r := ⟨edge, hedge, rank, hdec⟩
  refine ⟨U, ?_⟩
  let rep (q : {q : ContractV C.support // q ≠ qr}) : {v : V // v ≠ r} :=
    ⟨q.val.elim entry Subtype.val, by
      intro h
      cases hq : q.val with
      | none => exact hentryr (by simpa [hq] using h)
      | some v =>
        apply q.property
        have hv : v.val = r := by simpa [hq] using h
        rw [hq]
        exact congrArg some (Subtype.ext hv)⟩
  have hrep : ∀ q, contract C.support (rep q) = q.val := by
    intro q
    cases hq : q.val with
    | none => simpa [rep, hq] using (contract_none_iff C.support entry).mpr hentry
    | some v => simpa [rep, hq] using contract_some C.support v
  have hinj : Function.Injective rep := by
    intro q z h
    apply Subtype.ext
    rw [← hrep q, ← hrep z, h]
  have hrep_edge : ∀ q, edge (rep q) = (T.edge q).val := by
    intro q
    cases hq : q.val with
    | none =>
      have he : q = q0 := Subtype.ext hq
      subst q
      simp [rep, q0, edge, hentry, e0]
    | some v =>
      have hv : (rep q).val = v := by simp [rep, hq]
      have hnot : (rep q).val ∉ C.support := by simpa only [hv] using v.property
      have ho : outside (rep q) hnot = q := by
        apply Subtype.ext
        simp only [outside, hq]
        exact congrArg some (Subtype.ext hv)
      simp [edge, hnot, ho]
  have hz : ∀ v : {v : V // v ≠ r}, v ∉ Finset.univ.image rep → c (edge v) = 0 := by
    intro v hn
    have hv : v.val ∈ C.support := by
      by_contra hv
      apply hn
      refine Finset.mem_image.mpr ⟨outside v hv, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      rfl
    have he : v.val ≠ entry := by
      intro he
      apply hn
      refine Finset.mem_image.mpr ⟨q0, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      exact he.symm
    simpa [edge, hv, he] using hzero v
  change (∑ v, c (edge v)) = ∑ q, c (T.edge q).val
  calc
    _ = ∑ v ∈ Finset.univ.image rep, c (edge v) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hn
      exact hz v hn
    _ = ∑ q, c (edge (rep q)) := Finset.sum_image (fun q _ z _ h => hinj h)
    _ = _ := by
      simp only [hrep_edge]
      rfl

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: RootedOptimization -/
section

namespace OptimumBranchings.Polytope.Proof

universe u v

private theorem rooted_tree_le_aux (N : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ (E : Type v) [Fintype E] [DecidableEq E]
        (G : Graph V E) (r : V) (c : E → ℝ), (∀ e, 0 ≤ c e) →
        ∀ x : E → ℝ, CutFeasible G r x →
        ∃ T : RootedTree G r, T.cost c ≤ ∑ e, c e * x e := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V _ _ hcard E _ _ G r c hc x hx
    classical
    obtain ⟨pick, hhead, hmin⟩ := minimum_incoming hx c
    let p (v : V) := if hv : v = r then r else G.rear (pick ⟨v, hv⟩)
    have hparent : ∀ v : {v : V // v ≠ r}, G.rear (pick v) = p v := by
      intro v
      simp [p, v.property]
    let d := residualCost G r c pick
    have hd : ∀ e, 0 ≤ d e := residual_nonneg G r c hc pick hmin
    have hd0 : ∀ v, d (pick v) = 0 := residual_pick G r c pick hhead
    have hnorm := normalized_cost_lower hx c hc pick
    rcases parent_dichotomy p r with ⟨rank, hrank⟩ | ⟨C, hr⟩
    · let T : RootedTree G r :=
        ⟨pick, hhead, rank, fun v => by rw [hparent]; exact hrank v v.property⟩
      have hn : 0 ≤ ∑ e, d e * x e :=
        Finset.sum_nonneg (fun e _ => mul_nonneg (hd e) (hx.1 e))
      refine ⟨T, ?_⟩
      change (∑ v, c (pick v)) ≤ ∑ e, c e * x e
      dsimp [d] at hn
      linarith
    · have hnf : ∀ v ∈ C.support, p v ≠ v := by
        intro v hv he
        have hvr : v ≠ r := fun h => hr (h ▸ hv)
        have hp := hparent ⟨v, hvr⟩
        have hh := hhead ⟨v, hvr⟩
        exact G.front_ne_rear (pick ⟨v, hvr⟩) (hh.trans (hp.trans he).symm)
      have hsmall : Fintype.card (ContractV C.support) < N := by
        rw [← hcard]
        exact contract_card_lt C.support (C.card_ge_two hnf)
      have hxq := contract_feasible G C.support C.nonempty r hr x hx
      obtain ⟨T, hT⟩ := ih (Fintype.card (ContractV C.support)) hsmall
        (ContractV C.support) rfl (ContractE G C.support)
        (contractGraph G C.support) (contractRoot C.support r hr)
        (fun e => d e.val) (fun e => hd e.val) (fun e => x e.val) hxq
      obtain ⟨U, hU⟩ := lift_rooted_tree G r pick hhead p hparent C hr d hd0 T
      refine ⟨U, ?_⟩
      calc
        U.cost c = (∑ v : {v : V // v ≠ r}, c (pick v)) + U.cost d :=
          tree_cost_normalized G r c pick U
        _ ≤ (∑ v : {v : V // v ≠ r}, c (pick v)) + ∑ e, d e * x e := by
          apply add_le_add le_rfl
          rw [hU]
          exact hT.trans (contract_cost_le G C.support d x hd hx.1)
        _ ≤ ∑ e, c e * x e := hnorm

theorem exists_rooted_tree_le {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (r : V) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (x : E → ℝ) (hx : CutFeasible G r x) :
    ∃ T : RootedTree G r, T.cost c ≤ ∑ e, c e * x e :=
  rooted_tree_le_aux (Fintype.card V) V rfl E G r c hc x hx

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: AugmentedGraph -/
section

namespace OptimumBranchings.Polytope.Proof

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def augmentedGraph (G : Graph V E) : Graph (Option V) (E ⊕ V) where
  front := Sum.elim (fun e => some (G.front e)) some
  rear := Sum.elim (fun e => some (G.rear e)) (fun _ => none)
  front_ne_rear := by
    intro e
    cases e with
    | inl e => simpa using G.front_ne_rear e
    | inr v => simp

def incomingSum (G : Graph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.front e = v), x e

def internalSum (G : Graph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.front e ∈ S ∧ G.rear e ∈ S), x e

def augmentedWeight (G : Graph V E) (x : E → ℝ) : E ⊕ V → ℝ :=
  Sum.elim x (fun v => 1 - incomingSum G x v)

omit [Fintype V] [DecidableEq E] in
theorem augmentedWeight_nonneg (G : Graph V E) (x : E → ℝ)
    (hx : x ∈ branchingPolyhedron G) : ∀ e, 0 ≤ augmentedWeight G x e := by
  intro e
  cases e with
  | inl e => exact hx.1 e
  | inr v => exact sub_nonneg.mpr (hx.2.1 v)

omit [DecidableEq E] in
theorem augmented_incoming (G : Graph V E) (x : E → ℝ) (v : V) :
    incomingSum (augmentedGraph G) (augmentedWeight G x) (some v) = 1 := by
  rw [incomingSum, Finset.sum_filter, Fintype.sum_sum_type]
  change (∑ e : E, if some (G.front e) = some v then x e else 0) +
    (∑ w : V, if some w = some v then 1 - incomingSum G x w else 0) = 1
  simp only [Option.some.injEq]
  simp
  simp only [incomingSum, Finset.sum_filter]
  ring

omit [Fintype V] [DecidableEq E] in
theorem sum_incoming (G : Graph V E) (x : E → ℝ) (S : Finset V) :
    ∑ v ∈ S, incomingSum G x v =
      ∑ e ∈ Finset.univ.filter (fun e => G.front e ∈ S), x e := by
  simp only [incomingSum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

omit [Fintype V] [DecidableEq E] in
theorem cut_balance (G : Graph V E) (x : E → ℝ) (S : Finset V) :
    ∑ v ∈ S, incomingSum G x v =
      (∑ e ∈ inCut G S, x e) + internalSum G x S := by
  rw [sum_incoming]
  simp only [inCut, internalSum, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hf : G.front e ∈ S <;> by_cases hr : G.rear e ∈ S <;> simp [hf, hr]

omit [Fintype V] [DecidableEq E] in
theorem internal_singleton (G : Graph V E) (x : E → ℝ) (v : V) :
    internalSum G x {v} = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  simp only [Finset.mem_singleton] at hh
  exact False.elim (G.front_ne_rear e (hh.1.trans hh.2.symm))

omit [Fintype V] [DecidableEq E] in
theorem internal_bound (G : Graph V E) (x : E → ℝ)
    (hx : x ∈ branchingPolyhedron G) (S : Finset V) (hS : S.Nonempty) :
    internalSum G x S ≤ (S.card : ℝ) - 1 := by
  by_cases hcard : 2 ≤ S.card
  · exact hx.2.2 S hcard
  · have heq : S.card = 1 := by have := hS.card_pos; omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp heq
    simp [internal_singleton]

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: AugmentedCuts -/
section

namespace OptimumBranchings.Polytope.Proof

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def somePreimage (S : Finset (Option V)) : Finset V :=
  Finset.univ.filter (fun v => some v ∈ S)

theorem somePreimage_card (S : Finset (Option V)) (hS : none ∉ S) :
    (somePreimage S).card = S.card := by
  apply Finset.card_bij (fun v _ => some v)
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v _ w _ h
    exact Option.some.inj h
  · intro q hq
    cases q with
    | none => exact False.elim (hS hq)
    | some v => exact ⟨v, by simpa [somePreimage] using hq, rfl⟩

theorem somePreimage_nonempty (S : Finset (Option V)) (hS : none ∉ S)
    (hne : S.Nonempty) : (somePreimage S).Nonempty := by
  apply Finset.card_pos.mp
  rw [somePreimage_card S hS]
  exact hne.card_pos

omit [DecidableEq E] in
theorem augmented_internal (G : Graph V E) (x : E → ℝ)
    (S : Finset (Option V)) (hS : none ∉ S) :
    internalSum (augmentedGraph G) (augmentedWeight G x) S =
      internalSum G x (somePreimage S) := by
  simp only [internalSum, Finset.sum_filter, Fintype.sum_sum_type]
  change (∑ e : E, if some (G.front e) ∈ S ∧ some (G.rear e) ∈ S then x e else 0) +
      (∑ v : V, if some v ∈ S ∧ none ∈ S then 1 - incomingSum G x v else 0) = _
  simp only [hS, and_false, if_false, Finset.sum_const_zero, add_zero,
    somePreimage, Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq E] in
theorem augmented_cut_feasible (G : Graph V E) (x : E → ℝ)
    (hx : x ∈ branchingPolyhedron G) :
    CutFeasible (augmentedGraph G) none (augmentedWeight G x) := by
  refine ⟨augmentedWeight_nonneg G x hx, ?_⟩
  intro S hne hS
  have hbal := cut_balance (augmentedGraph G) (augmentedWeight G x) S
  have hin : ∑ q ∈ S, incomingSum (augmentedGraph G) (augmentedWeight G x) q = S.card := by
    calc
      _ = ∑ _q ∈ S, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro q hq
        cases q with
        | none => exact False.elim (hS hq)
        | some v => exact augmented_incoming G x v
      _ = _ := by simp
  rw [hin, augmented_internal G x S hS] at hbal
  have hb := internal_bound G x hx (somePreimage S) (somePreimage_nonempty S hS hne)
  rw [somePreimage_card S hS] at hb
  linarith

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: RankedBranching -/
section

namespace OptimumBranchings.Polytope.Proof

open scoped Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem branching_of_rank (G : Graph V E) (B : Finset E)
    (hhead : ∀ e ∈ B, ∀ f ∈ B, G.front e=G.front f → e=f)
    (rank : V → ℕ) (hrank : ∀ e ∈ B,rank (G.rear e)<rank (G.front e)) :
    G.IsBranching B := by
  refine ⟨?_,hhead⟩
  intro F hFB hF hregular
  obtain ⟨e,he,hmax⟩ := Finset.exists_max_image F (fun e => rank (G.front e)) hF
  have hin : F.filter (fun f => G.front f=G.front e)={e} := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hf,hfe⟩
      exact hhead f (hFB hf) e (hFB he) hfe
    · rintro rfl
      exact ⟨he,rfl⟩
  have hout : F.filter (fun f => G.rear f=G.front e)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro f hf hfe
    have hlt := hrank f (hFB hf)
    rw [hfe] at hlt
    exact (not_lt_of_ge (hmax f hf)) hlt
  have hm : G.meetCount F (G.front e)=1 := by simp [Graph.meetCount,hin,hout]
  have hh := hregular (G.front e)
  rw [hm] at hh
  omega

namespace RootedTree

omit [Fintype E] in
theorem isBranching {G : Graph V E} {r : V} (T : RootedTree G r) :
    G.IsBranching T.edges := by
  refine branching_of_rank G T.edges ?_ T.rank ?_
  · intro e he f hf hef
    obtain ⟨v,_hv,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨w,_hw,rfl⟩ := Finset.mem_image.mp hf
    have hvw : v=w := Subtype.ext (by simpa only [T.head] using hef)
    exact congrArg T.edge hvw
  · intro e he
    obtain ⟨v,_hv,rfl⟩ := Finset.mem_image.mp he
    simpa only [T.head] using T.decreasing v

end RootedTree

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: AugmentedCosts -/
section

namespace OptimumBranchings.Polytope.Proof

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def weightShift (c : E → ℝ) : ℝ := 1 + ∑ e, |c e|

def shiftedCost (c : E → ℝ) (M : ℝ) : E ⊕ V → ℝ :=
  Sum.elim (fun e => M - c e) (fun _ => M)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem shiftedCost_nonneg (c : E → ℝ) : ∀ e : E ⊕ V, 0 ≤ shiftedCost c (weightShift c) e := by
  have hm : 0 ≤ weightShift c := by
    dsimp [weightShift]
    positivity
  intro e
  cases e with
  | inl e =>
    apply sub_nonneg.mpr
    have h : |c e| ≤ ∑ f, |c f| :=
      Finset.single_le_sum (fun f _ => abs_nonneg (c f)) (Finset.mem_univ e)
    have hh := le_abs_self (c e)
    dsimp [weightShift]
    linarith
  | inr v => exact hm

omit [DecidableEq E] in
theorem augmented_fractional_cost (G : Graph V E) (c x : E → ℝ) (M : ℝ) :
    (∑ e : E ⊕ V, shiftedCost c M e * augmentedWeight G x e) =
      M * Fintype.card V - ∑ e, c e * x e := by
  have hin : ∑ v, incomingSum G x v = ∑ e, x e := by
    simpa using sum_incoming G x Finset.univ
  rw [Fintype.sum_sum_type]
  change (∑ e : E, (M - c e) * x e) +
    (∑ v : V, M * (1 - incomingSum G x v)) = _
  simp only [sub_mul, mul_sub, mul_one, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hin]
  ring

def projectedEdges (F : Finset (E ⊕ V)) : Finset E :=
  Finset.univ.filter (fun e => Sum.inl e ∈ F)

def originalCost (c : E → ℝ) : E ⊕ V → ℝ := Sum.elim c (fun _ => 0)

theorem projected_sum (F : Finset (E ⊕ V)) (c : E → ℝ) :
    ∑ e ∈ F, originalCost c e = ∑ e ∈ projectedEdges F, c e := by
  calc
    _ = ∑ e : E ⊕ V, if e ∈ F then originalCost c e else 0 := by
      simp
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [originalCost, projectedEdges, Finset.sum_filter]

theorem projected_branching (G : Graph V E)
    (T : RootedTree (augmentedGraph G) none) :
    G.IsBranching (projectedEdges T.edges) := by
  apply branching_of_rank G (projectedEdges T.edges) ?_ (fun v => T.rank (some v)) ?_
  · intro e he f hf h
    have he' := (Finset.mem_filter.mp he).2
    have hf' := (Finset.mem_filter.mp hf).2
    have hh := T.isBranching.2 (Sum.inl e) he' (Sum.inl f) hf' (congrArg some h)
    exact Sum.inl.inj hh
  · intro e he
    have he' := (Finset.mem_filter.mp he).2
    obtain ⟨v, _hv, hv⟩ := Finset.mem_image.mp he'
    have hd := T.decreasing v
    have hh := T.head v
    rw [hv] at hd hh
    change T.rank (some (G.rear e)) < T.rank v at hd
    change some (G.front e) = v.val at hh
    simpa only [← hh] using hd

omit [Fintype E] in
theorem augmented_tree_card (G : Graph V E)
    (T : RootedTree (augmentedGraph G) none) : T.edges.card = Fintype.card V := by
  rw [RootedTree.edges, Finset.card_image_of_injective _ T.edge_injective,
    Finset.card_univ]
  simp [Fintype.card_subtype_compl]

theorem augmented_tree_cost (G : Graph V E)
    (T : RootedTree (augmentedGraph G) none) (c : E → ℝ) (M : ℝ) :
    T.cost (shiftedCost c M) = M * Fintype.card V -
      ∑ e ∈ projectedEdges T.edges, c e := by
  have hc : ∀ e : E ⊕ V, shiftedCost c M e = M - originalCost c e := by
    intro e
    cases e <;> simp [shiftedCost, originalCost]
  calc
    _ = ∑ e ∈ T.edges, (M - originalCost c e) := by
      rw [T.sum_edges]
      apply Finset.sum_congr rfl
      intro v _
      exact hc _
    _ = (T.edges.card : ℝ) * M - ∑ e ∈ T.edges, originalCost c e := by
      rw [Finset.sum_sub_distrib]
      simp
    _ = _ := by rw [augmented_tree_card, projected_sum]; ring

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: Augmentation -/
section

namespace OptimumBranchings.Polytope.Proof

theorem objective_dominated {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c x : E → ℝ) (hx : x ∈ branchingPolyhedron G) :
    ∃ B : Finset E, G.IsBranching B ∧
      ∑ e, c e * x e ≤ ∑ e, c e * incidenceVector B e := by
  obtain ⟨T, hT⟩ := exists_rooted_tree_le (augmentedGraph G) none
    (shiftedCost c (weightShift c)) (shiftedCost_nonneg c)
    (augmentedWeight G x) (augmented_cut_feasible G x hx)
  refine ⟨projectedEdges T.edges, projected_branching G T, ?_⟩
  rw [augmented_tree_cost, augmented_fractional_cost] at hT
  have hs : (∑ e, c e * incidenceVector (projectedEdges T.edges) e) =
      ∑ e ∈ projectedEdges T.edges, c e := by
    simp [incidenceVector, mul_ite]
  rw [hs]
  linarith

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: CycleEdges -/
section

namespace OptimumBranchings.Polytope.Proof

open scoped Classical

variable {V E I : Type*}

theorem cycle_edges_not_forest [DecidableEq V] [Fintype I] [Nonempty I]
    (G : Graph V E) (B : Finset E) (vertex : I → V)
    (hinj : Function.Injective vertex) (parent : I ≃ I) (edge : I → E)
    (hhead : ∀ i, G.front (edge i)=vertex i)
    (hback : ∀ i, G.rear (edge i)=vertex (parent i))
    (hmem : ∀ i, edge i ∈ B) : ¬ G.IsForest B := by
  classical
  let F := Finset.univ.image edge
  have hF : F.Nonempty := Finset.univ_nonempty.image edge
  have hFB : F ⊆ B := by
    intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    exact hmem i
  intro hforest
  apply hforest F hFB hF
  intro v
  by_cases hv : ∃ i,vertex i=v
  · obtain ⟨i,rfl⟩ := hv
    have hi : F.filter (fun e => G.front e=vertex i)={edge i} := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · rintro ⟨he,h⟩
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
        rw [hhead] at h
        exact congrArg edge (hinj h)
      · rintro rfl
        exact ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hhead i⟩
    have ho : F.filter (fun e => G.rear e=vertex i)={edge (parent.symm i)} := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · rintro ⟨he,h⟩
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
        rw [hback] at h
        apply congrArg edge
        have hh := congrArg parent.symm (hinj h)
        simpa only [Equiv.symm_apply_apply] using hh
      · rintro rfl
        refine ⟨Finset.mem_image.mpr ⟨parent.symm i,Finset.mem_univ _,rfl⟩,?_⟩
        simp only [hback,Equiv.apply_symm_apply]
    exact Or.inr (by simp [Graph.meetCount,hi,ho])
  · have hi : F.filter (fun e => G.front e=v)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he h
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact hv ⟨i,(hhead i).symm.trans h⟩
    have ho : F.filter (fun e => G.rear e=v)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he h
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact hv ⟨parent i,(hback i).symm.trans h⟩
    exact Or.inl (by simp [Graph.meetCount,hi,ho])

noncomputable def ParentCycle.parentEquiv {p : V → V} (C : ParentCycle p) :
    C.support ≃ C.support :=
  Equiv.ofBijective (fun v => ⟨p v,C.maps v v.2⟩) (by
    constructor
    · intro u v h
      exact Subtype.ext (C.injOn u.2 v.2 (congrArg Subtype.val h))
    · intro v
      obtain ⟨u,hu,he⟩ := C.surjOn v.2
      exact ⟨⟨u,hu⟩,Subtype.ext he⟩)

theorem branching_missing_incoming [DecidableEq V]
    (G : Graph V E) (B : Finset E) (hB : G.IsBranching B)
    (U : Finset V) (hU : U.Nonempty) :
    ∃ v ∈ U, ¬∃ e ∈ B,G.front e=v ∧ G.rear e∈U := by
  classical
  by_contra! h
  let pick : U → E := fun v => Classical.choose (h v v.2)
  have hp : ∀ v : U,pick v∈B ∧ G.front (pick v)=v ∧ G.rear (pick v)∈U :=
    fun v => Classical.choose_spec (h v v.2)
  let p : U → U := fun v => ⟨G.rear (pick v),(hp v).2.2⟩
  let : Nonempty U := ⟨⟨hU.choose,hU.choose_spec⟩⟩
  obtain ⟨C,_⟩ := exists_parent_cycle p Finset.univ Finset.univ_nonempty
    (fun _ _ => Finset.mem_univ _)
  let : Nonempty C.support := ⟨⟨C.nonempty.choose,C.nonempty.choose_spec⟩⟩
  apply cycle_edges_not_forest G B (fun i : C.support => (i.val : V))
    (fun _ _ h => Subtype.ext (Subtype.ext h)) C.parentEquiv
    (fun i => pick i.val) (fun i => (hp i.val).2.1) (fun _ => rfl)
    (fun i => (hp i.val).1) hB.1

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: BranchingMembership -/
section

namespace OptimumBranchings.Polytope.Proof

open scoped Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem incidence_sum (B F : Finset E) :
    ∑ e ∈ F,incidenceVector B e = ((F.filter (fun e => e∈B)).card : ℝ) := by
  simp [incidenceVector,Finset.filter_mem_eq_inter]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem branching_internal_card (G : Graph V E) (B : Finset E)
    (hB : G.IsBranching B) (U : Finset V) (hU : U.Nonempty) :
    (B.filter (fun e => G.front e∈U ∧ G.rear e∈U)).card ≤ U.card-1 := by
  obtain ⟨v,hv,hmissing⟩ := branching_missing_incoming G B hB U hU
  let F := B.filter (fun e => G.front e∈U ∧ G.rear e∈U)
  have hinj : Set.InjOn G.front F := by
    intro e he f hf hef
    exact hB.2 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hef
  have himage : F.image G.front ⊆ U.erase v := by
    intro w hw
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨heB,heU,hrU⟩ := Finset.mem_filter.mp he
    apply Finset.mem_erase.mpr
    refine ⟨?_,heU⟩
    intro h
    exact hmissing ⟨e,heB,h,hrU⟩
  calc F.card = (F.image G.front).card := (Finset.card_image_of_injOn hinj).symm
       _ ≤ (U.erase v).card := Finset.card_le_card himage
       _ = U.card-1 := Finset.card_erase_of_mem hv

omit [Fintype V] in
theorem branching_vector_mem (G : Graph V E) (B : Finset E)
    (hB : G.IsBranching B) : incidenceVector B ∈ branchingPolyhedron G := by
  refine ⟨?_,?_,?_⟩
  · intro e
    simp only [incidenceVector]
    split_ifs <;> norm_num
  · intro v
    rw [incidence_sum]
    have heq : (Finset.univ.filter (fun e => G.front e=v)).filter (fun e => e∈B) =
        B.filter (fun e => G.front e=v) := by ext e; simp [and_comm]
    rw [heq]
    norm_cast
    apply Finset.card_le_one.mpr
    intro e he f hf
    obtain ⟨he,hv⟩ := Finset.mem_filter.mp he
    obtain ⟨hf,hv'⟩ := Finset.mem_filter.mp hf
    exact hB.2 e he f hf (hv.trans hv'.symm)
  · intro U hU
    rw [incidence_sum]
    have heq : (Finset.univ.filter (fun e => G.front e∈U ∧ G.rear e∈U)).filter
        (fun e => e∈B) = B.filter (fun e => G.front e∈U ∧ G.rear e∈U) := by
      ext e
      simp [and_comm]
    rw [heq]
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    have hcard := branching_internal_card G B hB U hne
    have hle : (1:ℕ)≤U.card := by omega
    have hh : ((U.card-1:ℕ):ℝ)=(U.card:ℝ)-1 := by simp [Nat.cast_sub hle]
    rw [←hh]
    exact_mod_cast hcard

omit [Fintype V] [DecidableEq E] in
theorem coordinate_le_one (G : Graph V E) {x : E → ℝ}
    (hx : x∈branchingPolyhedron G) (e : E) : x e≤1 := by
  have hmem : e∈Finset.univ.filter (fun f => G.front f=G.front e) := by simp
  exact (Finset.single_le_sum (fun f _ => hx.1 f) hmem).trans (hx.2.1 (G.front e))

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: BranchingVertices -/
section

namespace OptimumBranchings.Polytope.Proof

open scoped Classical

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

theorem branching_vector_isVertex (G : Graph V E) (B : Finset E)
    (hB : G.IsBranching B) : IsVertex (branchingPolyhedron G) (incidenceVector B) := by
  refine ⟨branching_vector_mem G B hB,fun e => if e∈B then 1 else -1,?_⟩
  intro y hy hne
  have hle : ∀ e,(if e∈B then (1:ℝ) else -1)*y e ≤
      (if e∈B then (1:ℝ) else -1)*incidenceVector B e := by
    intro e
    by_cases he : e∈B
    · simpa [he,incidenceVector] using coordinate_le_one G hy e
    · simpa [he,incidenceVector] using hy.1 e
  have hex : ∃ e,y e≠incidenceVector B e := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨e,he⟩ := hex
  apply Finset.sum_lt_sum (fun e _ => hle e)
  refine ⟨e,Finset.mem_univ _,?_⟩
  apply lt_of_le_of_ne (hle e)
  intro heq
  apply he
  by_cases hmem : e∈B
  · simpa [hmem] using heq
  · simpa [hmem] using heq

end OptimumBranchings.Polytope.Proof

end

/- Complete checked body: BranchingsRoot -/
section

namespace OptimumBranchings.Polytope.Proof

theorem vertices_eq_branching_vectors {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) :
    {x : E → ℝ | IsVertex (branchingPolyhedron G) x} =
      {x : E → ℝ | ∃ B : Finset E, G.IsBranching B ∧ x = incidenceVector B} := by
  ext x
  constructor
  · rintro ⟨hx,c,hc⟩
    obtain ⟨B,hB,hle⟩ := objective_dominated G c x hx
    refine ⟨B,hB,?_⟩
    by_contra hne
    have hlt := hc (incidenceVector B) (branching_vector_mem G B hB) (Ne.symm hne)
    exact (not_lt_of_ge hle) hlt
  · rintro ⟨B,hB,rfl⟩
    exact branching_vector_isVertex G B hB

end OptimumBranchings.Polytope.Proof

namespace OptimumBranchings.Polytope

/-- Edmonds (1967), Theorem 2, p. 235: the vertices of the polyhedron `P_G` are precisely the
vectors of the subsets of edges in `G` which comprise branchings. -/
theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) :
    {x : E → ℝ | IsVertex (branchingPolyhedron G) x} =
      {x : E → ℝ | ∃ B : Finset E, G.IsBranching B ∧ x = incidenceVector B} := by
  exact Proof.vertices_eq_branching_vectors G

end OptimumBranchings.Polytope

end

open OptimumBranchings.Polytope


theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : OptimumBranchings.Polytope.Graph V E) :
    {x : E → ℝ | IsVertex (branchingPolyhedron G) x} =
      {x : E → ℝ | ∃ B : Finset E, G.IsBranching B ∧ x = incidenceVector B} := by
  exact OptimumBranchings.Polytope.solution G

#print axioms OptimumBranchings.Polytope.solution
#print axioms _root_.solution
