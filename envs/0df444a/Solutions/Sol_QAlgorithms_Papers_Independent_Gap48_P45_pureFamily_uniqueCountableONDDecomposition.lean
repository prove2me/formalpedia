-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.pureFamily_uniqueCountableONDDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:12:17.065477+00:00
-- url     : https://prove2.me/submissions/950f5bdf-75ce-4983-a854-d2e654f901db

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace X4P45L5

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne PureState)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)
open QAlgorithms.Papers.Independent.Gap48.P45

variable {I : Type}

local notation "e" i => lp.single (E := fun _ : I => ℂ) 2 i 1

/-- the rank-one operator `w ↦ ⟪u, w⟫ u` -/
def rk (u : Hilbert I) : Hilbert I →L[ℂ] Hilbert I := (innerSL ℂ u).smulRight u

lemma rk_apply (u w : Hilbert I) : rk u w = (inner ℂ u w) • u := rfl

lemma coeff_rk (u : Hilbert I) : operatorCoeff (rk u) = rankOne u := by
  ext i j
  simp [operatorCoeff, rk_apply, rankOne, lp.inner_single_right, mul_comm]

lemma coeff_inj {A B : Hilbert I →L[ℂ] Hilbert I} (h : operatorCoeff A = operatorCoeff B) :
    A = B := by
  ext1 f
  have hs := lp.hasSum_single (p := 2) (by norm_num) f
  have hA := hs.mapL A
  have hB := hs.mapL B
  have hfun : (fun i => A (lp.single 2 i (f i))) = (fun i => B (lp.single 2 i (f i))) := by
    funext i
    have hsm : lp.single 2 i (f i) = (f i) • (e i) := by
      rw [← lp.single_smul]; simp
    rw [hsm, map_smul, map_smul]
    congr 1
    ext k
    exact congrFun (congrFun h k) i
  rw [hfun] at hA
  exact hA.unique hB

lemma bo_rankOne (u : Hilbert I) : boundedOperator (rankOne u) = rk u := by
  have hex : ∃ A : Hilbert I →L[ℂ] Hilbert I, operatorCoeff A = rankOne u := ⟨rk u, coeff_rk u⟩
  unfold boundedOperator
  rw [dif_pos hex]
  exact coeff_inj (hex.choose_spec.trans (coeff_rk u).symm)

lemma orth_iff {u v : Hilbert I} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (rk u).comp (rk v) = 0 ↔ inner ℂ u v = 0 := by
  constructor
  · intro h
    have := congrArg (fun T => T v) h
    simp only [ContinuousLinearMap.comp_apply, rk_apply, map_smul, ContinuousLinearMap.zero_apply,
      inner_self_eq_norm_sq_to_K, hv, smul_smul] at this
    have hu0 : u ≠ 0 := by intro h0; simp [h0] at hu
    rcases smul_eq_zero.1 this with h1 | h1
    · simpa using h1
    · exact absurd h1 hu0
  · intro h
    ext1 w
    simp [rk_apply, h]


lemma pure_vec {rho : State I} (h : rho ∈ pureStates I) :
    ∃ u : Hilbert I, ‖u‖ = 1 ∧ rho.coefficients = rankOne u := by
  obtain ⟨⟨r, hr⟩, rfl⟩ := h
  exact hr

lemma orth_vec {a b : State I} {u v : Hilbert I} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha : a.coefficients = rankOne u) (hb : b.coefficients = rankOne v) :
    StatesOrthogonal a b ↔ inner ℂ u v = 0 := by
  unfold StatesOrthogonal
  rw [ha, hb, bo_rankOne, bo_rankOne, orth_iff hu hv]

lemma orth_symm {a b : State I} (ha : a ∈ pureStates I) (hb : b ∈ pureStates I)
    (h : StatesOrthogonal a b) : StatesOrthogonal b a := by
  obtain ⟨u, hu, hau⟩ := pure_vec ha
  obtain ⟨v, hv, hbv⟩ := pure_vec hb
  rw [orth_vec hu hv hau hbv] at h
  rw [orth_vec hv hu hbv hau, ← inner_conj_symm, h, map_zero]

/-- the chain relation of `connectedComponent` -/
def Rl (S : Set (State I)) (a b : State I) : Prop := a ∈ S ∧ b ∈ S ∧ ¬ StatesOrthogonal a b

lemma symm_R {S : Set (State I)} (hPure : S ⊆ pureStates I) : Symmetric (Rl S) := by
  rintro a b ⟨ha, hb, h⟩
  exact ⟨hb, ha, fun h' => h (orth_symm (hPure hb) (hPure ha) h')⟩

lemma rtg_symm {α : Type} {r : α → α → Prop} (hs : Symmetric r) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih => exact Relation.ReflTransGen.head (hs hcd) ih

lemma mem_comp {S : Set (State I)} {rho sigma : State I} :
    sigma ∈ connectedComponent S rho ↔
      rho ∈ S ∧ sigma ∈ S ∧ Relation.ReflTransGen (Rl S) rho sigma := Iff.rfl

lemma comp_eq {S : Set (State I)} (hPure : S ⊆ pureStates I) {rho sigma : State I}
    (h : sigma ∈ connectedComponent S rho) :
    connectedComponent S sigma = connectedComponent S rho := by
  rw [mem_comp] at h
  ext x
  rw [mem_comp, mem_comp]
  constructor
  · rintro ⟨_, hx, hsx⟩; exact ⟨h.1, hx, h.2.2.trans hsx⟩
  · rintro ⟨_, hx, hrx⟩
    exact ⟨h.2.1, hx, (rtg_symm (symm_R hPure) h.2.2).trans hrx⟩

lemma cross' {α : Type} {A : Set α} {r : α → α → Prop} {a b : α} (ha : a ∈ A)
    (h : Relation.ReflTransGen r a b) (hb : b ∉ A) :
    ∃ u ∈ A, ∃ w, w ∉ A ∧ r u w := by
  induction h with
  | refl => exact absurd ha hb
  | @tail c d _ hcd ih =>
    by_cases hc : c ∈ A
    · exact ⟨c, hc, d, hb, hcd⟩
    · exact ih hc

lemma partition {S : Set (State I)} (hPure : S ⊆ pureStates I) :
    IsONDPartition S (componentSets S) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨C, ⟨rho, _, rfl⟩, hx⟩; exact hx.2.1
    · intro hx
      exact ⟨connectedComponent S x, ⟨x, hx, rfl⟩, hx, hx, Relation.ReflTransGen.refl⟩
  · rintro C ⟨rho, hrho, rfl⟩
    refine ⟨⟨rho, hrho, hrho, Relation.ReflTransGen.refl⟩, ?_⟩
    intro T hT ⟨a, ha⟩ ⟨b, hb⟩
    have hab : Relation.ReflTransGen (Rl S) a b :=
      (rtg_symm (symm_R hPure) (hT ha).2.2).trans hb.1.2.2
    obtain ⟨u, hu, w, hw, huw⟩ := cross' (A := {x | x ∈ T ∨ x ∉ connectedComponent S rho})
      (Or.inl ha) hab (by rintro (h | h); exacts [hb.2 h, h hb.1])
    simp only [Set.mem_setOf_eq, not_or, not_not] at hw
    rcases hu with hu | hu
    · exact ⟨u, hu, w, ⟨hw.2, hw.1⟩, huw.2.2⟩
    · exact absurd ⟨hrho, huw.1, hw.2.2.2.tail (symm_R hPure huw)⟩ hu
  · rintro C ⟨a, ha, rfl⟩ D ⟨b, hb, rfl⟩ hne
    refine ⟨Set.disjoint_left.2 fun x hxa hxb =>
      hne ((comp_eq hPure hxa).symm.trans (comp_eq hPure hxb)), ?_⟩
    intro r hr s hs
    by_contra hn
    have : s ∈ connectedComponent S a := ⟨ha, hs.2.1, hr.2.2.tail ⟨hr.2.1, hs.2.1, hn⟩⟩
    exact hne ((comp_eq hPure this).symm.trans (comp_eq hPure hs))

lemma unique {S : Set (State I)} (hPure : S ⊆ pureStates I) (parts : Set (Set (State I)))
    (hp : IsONDPartition S parts) : parts = componentSets S := by
  obtain ⟨hU, hND, hOr⟩ := hp
  have memS : ∀ C ∈ parts, ∀ x ∈ C, x ∈ S := fun C hC x hx => hU ▸ Set.mem_sUnion_of_mem hx hC
  have key : ∀ C ∈ parts, ∀ x ∈ C, C = connectedComponent S x := by
    intro C hC x hx
    ext y
    constructor
    · intro hy
      by_contra hn
      obtain ⟨rho, hrho, sigma, hsigma, hrs⟩ :=
        (hND C hC).2 {z | z ∈ C ∧ Relation.ReflTransGen (Rl S) x z} (fun z hz => hz.1)
          ⟨x, hx, Relation.ReflTransGen.refl⟩
          ⟨y, hy, fun h => hn ⟨memS C hC x hx, memS C hC y hy, h.2⟩⟩
      exact hsigma.2 ⟨hsigma.1, hrho.2.tail ⟨memS C hC _ hrho.1, memS C hC _ hsigma.1, hrs⟩⟩
    · rintro ⟨_, _, hxy⟩
      induction hxy with
      | refl => exact hx
      | @tail b c _ hbc ih =>
        have hcS := hbc.2.1
        rw [← hU] at hcS
        obtain ⟨D, hD, hcD⟩ := hcS
        by_cases hDC : D = C
        · exact hDC ▸ hcD
        · exact absurd ((hOr C hC D hD (Ne.symm hDC)).2 b (ih hbc.1) c hcD) hbc.2.2
  ext C
  constructor
  · intro hC
    obtain ⟨x, hx⟩ := (hND C hC).1
    exact ⟨x, memS C hC x hx, key C hC x hx⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← hU] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    rw [← key C hC x hxC]
    exact hC

lemma countable [Countable I] {S : Set (State I)} (hPure : S ⊆ pureStates I) :
    (componentSets S).Countable := by
  have hex : ∀ C : Component S, ∃ u : Hilbert I, ‖u‖ = 1 ∧
      ∃ rho ∈ C.1, rho.coefficients = rankOne u := by
    rintro ⟨C, ⟨rho, hrho, rfl⟩⟩
    obtain ⟨u, hu, hru⟩ := pure_vec (hPure hrho)
    exact ⟨u, hu, rho, ⟨hrho, hrho, Relation.ReflTransGen.refl⟩, hru⟩
  choose u hu rho hrho hru using hex
  have hON : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro C D
    split_ifs with h
    · subst h
      rw [inner_self_eq_norm_sq_to_K, hu]; simp
    · have hne : C.1 ≠ D.1 := fun h' => h (Subtype.ext h')
      have := (((partition hPure).2.2 C.1 C.2 D.1 D.2 hne).2 (rho C) (hrho C) (rho D) (hrho D))
      exact (orth_vec (hu C) (hu D) (hru C) (hru D)).1 this
  have hsub : ∀ i : I, {C : Component S | inner ℂ (u C) (e i) ≠ 0}.Countable := by
    intro i
    refine (hON.inner_products_summable (e i)).countable_support.mono ?_
    intro C hC
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff two_ne_zero, norm_eq_zero]
    exact hC
  have hcov : ∀ C : Component S, ∃ i : I, inner ℂ (u C) (e i) ≠ 0 := by
    intro C
    by_contra hn
    push_neg at hn
    have h0 : u C = 0 := by
      ext i
      have := hn i
      rw [lp.inner_single_right] at this
      simpa using this
    have := hu C
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have : Countable (Component S) := by
    rw [← Set.countable_univ_iff]
    exact (Set.countable_iUnion hsub).mono fun C _ => Set.mem_iUnion.2 (hcov C)
  rw [← Subtype.range_coe (s := componentSets S)]
  exact Set.countable_range _

end X4P45L5

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)
open QAlgorithms.Papers.Independent.Gap48.P45

theorem solution
    {I : Type} [Countable I] [Nonempty I]
    (S : Set (State I)) (hPure : S ⊆ pureStates I) :
    (componentSets S).Countable ∧ IsONDPartition S (componentSets S) ∧
      ∀ parts : Set (Set (State I)), IsONDPartition S parts → parts = componentSets S :=
  ⟨X4P45L5.countable hPure, X4P45L5.partition hPure, X4P45L5.unique hPure⟩
