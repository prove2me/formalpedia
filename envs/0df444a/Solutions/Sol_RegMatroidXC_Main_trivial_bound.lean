-- Prove2me | solution 1 for RegMatroidXC.Main.trivial_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:14:04.93419+00:00
-- url     : https://prove2.me/submissions/2348ae52-c503-4413-822c-4cc791b8a603

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
open ExtensionComplexity.TSP

namespace RMXCAux

open Matrix

/-- Flexible form of an extended formulation: variables, equations and inequalities indexed by
arbitrary finite types, given by linear maps. -/
theorem isEF_of_linear {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (r : ℕ)
    {K L J : Type*} [Fintype K] [Fintype L] [Fintype J] (hJ : Fintype.card J ≤ r)
    (A : (ι → ℝ) →ₗ[ℝ] (L → ℝ)) (B : (K → ℝ) →ₗ[ℝ] (L → ℝ)) (b : L → ℝ)
    (C : (ι → ℝ) →ₗ[ℝ] (J → ℝ)) (D : (K → ℝ) →ₗ[ℝ] (J → ℝ)) (c : J → ℝ)
    (h : ∀ x, x ∈ P ↔ ∃ y, A x + B y = b ∧ C x + D y ≤ c) : IsEFOfSize P r := by
  classical
  -- padded inequality index
  let J' := J ⊕ Fin (r - Fintype.card J)
  have hcard : Fintype.card J' = r := by
    simp only [J', Fintype.card_sum, Fintype.card_fin]; omega
  let eJ : J' ≃ Fin r := Fintype.equivFinOfCardEq hcard
  let eK : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let eL : L ≃ Fin (Fintype.card L) := Fintype.equivFin L
  -- linear maps
  let C' : (ι → ℝ) →ₗ[ℝ] (J' → ℝ) :=
    { toFun := fun x => Sum.elim (C x) 0
      map_add' := by intro x y; ext j; cases j <;> simp
      map_smul' := by intro a x; ext j; cases j <;> simp }
  let D' : (K → ℝ) →ₗ[ℝ] (J' → ℝ) :=
    { toFun := fun y => Sum.elim (D y) 0
      map_add' := by intro x y; ext j; cases j <;> simp
      map_smul' := by intro a x; ext j; cases j <;> simp }
  let c' : J' → ℝ := Sum.elim c 0
  have hle : ∀ x y, (C' x + D' y ≤ c') ↔ (C x + D y ≤ c) := by
    intro x y
    constructor
    · intro hh j; have := hh (Sum.inl j); simpa [C', D', c'] using this
    · intro hh j; cases j with
      | inl j => simpa [C', D', c'] using hh j
      | inr j => simp [C', D', c']
  let fK : (Fin (Fintype.card K) → ℝ) →ₗ[ℝ] (K → ℝ) := LinearMap.funLeft ℝ ℝ eK
  let fL : (L → ℝ) →ₗ[ℝ] (Fin (Fintype.card L) → ℝ) := LinearMap.funLeft ℝ ℝ eL.symm
  let fJ : (J' → ℝ) →ₗ[ℝ] (Fin r → ℝ) := LinearMap.funLeft ℝ ℝ eJ.symm
  refine ⟨Fintype.card K, Fintype.card L, LinearMap.toMatrix' (fL ∘ₗ A),
    LinearMap.toMatrix' (fL ∘ₗ B ∘ₗ fK), fL b, LinearMap.toMatrix' (fJ ∘ₗ C'),
    LinearMap.toMatrix' (fJ ∘ₗ D' ∘ₗ fK), fJ c', ?_⟩
  intro x
  simp only [LinearMap.toMatrix'_mulVec, LinearMap.coe_comp, Function.comp_apply]
  rw [h]
  have keyL : ∀ u v : L → ℝ, fL u = fL v ↔ u = v := by
    intro u v; constructor
    · intro huv; funext l; have := congrFun huv (eL l); simpa [fL, LinearMap.funLeft] using this
    · intro huv; rw [huv]
  have keyJ : ∀ u v : J' → ℝ, fJ u ≤ fJ v ↔ u ≤ v := by
    intro u v; constructor
    · intro huv l; have := huv (eJ l); simpa [fJ, LinearMap.funLeft] using this
    · intro huv l; simpa [fJ, LinearMap.funLeft] using huv (eJ.symm l)
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨fun i => y (eK.symm i), ?_, ?_⟩
    · have hy : fK (fun i => y (eK.symm i)) = y := by
        funext k; simp [fK, LinearMap.funLeft]
      rw [hy, ← map_add, keyL]; exact h1
    · have hy : fK (fun i => y (eK.symm i)) = y := by
        funext k; simp [fK, LinearMap.funLeft]
      rw [hy, ← map_add, keyJ, hle]; exact h2
  · rintro ⟨y', h1, h2⟩
    refine ⟨fK y', ?_, ?_⟩
    · rw [← map_add, keyL] at h1; exact h1
    · rw [← map_add, keyJ, hle] at h2; exact h2

end RMXCAux

namespace RMXCAux

open RegMatroidXC.Main

theorem trivial_bound_aux (α : Type) (M : Matroid α) [Fintype M.E] :
    ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ r ≤ 2 ^ Fintype.card M.E := by
  classical
  -- indicator vectors of subsets of the ground set
  let g : Finset M.E → (M.E → ℝ) := fun I e => if e ∈ I then 1 else 0
  let ind : Finset M.E → Prop := fun I => M.Indep (((↑) : M.E → α) '' (I : Set M.E))
  have hS : ∀ x : M.E → ℝ, (∃ I : Set α, M.Indep I ∧
      ∀ e : M.E, x e = I.indicator (fun _ => (1 : ℝ)) (e : α)) ↔ ∃ I, ind I ∧ x = g I := by
    intro x
    constructor
    · rintro ⟨I, hI, hx⟩
      refine ⟨Finset.univ.filter (fun e : M.E => (e : α) ∈ I), ?_, ?_⟩
      · have : ((↑) : M.E → α) '' ((Finset.univ.filter (fun e : M.E => (e : α) ∈ I) :
            Finset M.E) : Set M.E) = I := by
          ext a; constructor
          · rintro ⟨e, he, rfl⟩; simpa using he
          · intro ha; exact ⟨⟨a, hI.subset_ground ha⟩, by simpa using ha, rfl⟩
        simp only [ind]; rw [this]; exact hI
      · funext e; rw [hx e]; simp [g, Set.indicator]
    · rintro ⟨I, hI, rfl⟩
      refine ⟨_, hI, ?_⟩
      intro e
      simp only [g, Set.indicator]
      congr 1
      apply propext
      constructor
      · intro he; exact ⟨e, he, rfl⟩
      · rintro ⟨e', he', hee⟩; rw [Subtype.ext hee] at he'; exact he'
  let K := Finset M.E
  let L := M.E ⊕ (Unit ⊕ Finset M.E)
  let J := Finset M.E
  let A : (M.E → ℝ) →ₗ[ℝ] (L → ℝ) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := by intro x y; ext j; rcases j with j | j | j <;> simp
      map_smul' := by intro a x; ext j; rcases j with j | j | j <;> simp }
  let B : (K → ℝ) →ₗ[ℝ] (L → ℝ) :=
    { toFun := fun y => Sum.elim (fun e => -∑ I, y I * g I e)
        (Sum.elim (fun _ => ∑ I, y I) (fun I => if ind I then 0 else y I))
      map_add' := by
        intro x y; ext j; rcases j with j | j | j
        · simp [add_mul, Finset.sum_add_distrib]; ring
        · simp [Finset.sum_add_distrib]
        · simp only [Pi.add_apply, Sum.elim_inr]; split_ifs <;> simp
      map_smul' := by
        intro a x; ext j; rcases j with j | j | j
        · simp [Finset.mul_sum, mul_assoc]
        · simp [Finset.mul_sum]
        · simp only [Pi.smul_apply, Sum.elim_inr, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> simp }
  let b : L → ℝ := Sum.elim 0 (Sum.elim 1 0)
  let C : (M.E → ℝ) →ₗ[ℝ] (J → ℝ) := 0
  let D : (K → ℝ) →ₗ[ℝ] (J → ℝ) := -LinearMap.id
  refine ⟨Fintype.card J, isEF_of_linear _ _ le_rfl A B b C D 0 ?_, ?_⟩
  · intro x
    have hAB : ∀ y : K → ℝ, (A x + B y = b) ↔
        ((∀ e, x e = ∑ I, y I * g I e) ∧ ∑ I, y I = 1 ∧ ∀ I, ¬ ind I → y I = 0) := by
      intro y
      constructor
      · intro hh
        refine ⟨fun e => ?_, ?_, fun I hI => ?_⟩
        · have := congrFun hh (Sum.inl e)
          simp [A, B, b] at this; linarith
        · have := congrFun hh (Sum.inr (Sum.inl ()))
          simpa [A, B, b] using this
        · have := congrFun hh (Sum.inr (Sum.inr I))
          simpa [A, B, b, hI] using this
      · rintro ⟨h1, h2, h3⟩
        funext j; rcases j with e | u | I
        · simp [A, B, b, h1 e]
        · simpa [A, B, b] using h2
        · by_cases hI : ind I
          · simp [A, B, b, hI]
          · simp [A, B, b, hI, h3 I hI]
    have hCD : ∀ y : K → ℝ, (C x + D y ≤ 0) ↔ ∀ I, 0 ≤ y I := by
      intro y; constructor
      · intro hh I; have := hh I; simp [C, D] at this; linarith
      · intro hh I; simp [C, D]; exact hh I
    simp_rw [hAB, hCD]
    unfold indepPolytope
    constructor
    · intro hx
      rw [mem_convexHull_iff_exists_fintype] at hx
      obtain ⟨ι', _, w, z, hw0, hw1, hz, hx⟩ := hx
      have hz' : ∀ i, ∃ I, ind I ∧ z i = g I := fun i => (hS (z i)).1 (hz i)
      choose Ii hIi hzI using hz'
      refine ⟨fun I => ∑ i ∈ Finset.univ.filter (fun i => Ii i = I), w i, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro e
        rw [← hx]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun i => {Ii i})]
        · simp only [Finset.sum_singleton]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hzI i]
        · intro I i; simp [eq_comm]
      · rw [← hw1]
        rw [Finset.sum_fiberwise]
      · intro I hI
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_filter] at hi
        exact absurd (hi.2 ▸ hIi i) hI
      · intro I; exact Finset.sum_nonneg (fun i _ => hw0 i)
    · rintro ⟨y, ⟨h1, h2, h3⟩, h4⟩
      have hind0 : ind ∅ := by simp [ind]
      refine mem_convexHull_of_exists_fintype (ι := Finset M.E) y
        (fun I => if ind I then g I else g ∅) h4 h2 ?_ ?_
      · intro I
        rw [Set.mem_setOf_eq, hS]
        split_ifs with hI
        · exact ⟨I, hI, rfl⟩
        · exact ⟨∅, hind0, rfl⟩
      · funext e
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1 e]
        refine Finset.sum_congr rfl (fun I _ => ?_)
        by_cases hI : ind I
        · simp [hI]
        · simp [hI, h3 I hI]
  · simp [J]

end RMXCAux


open RegMatroidXC.Main in
theorem solution (α : Type) (M : Matroid α) [Fintype M.E] :
    ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ r ≤ 2 ^ Fintype.card M.E :=
  RMXCAux.trivial_bound_aux α M
