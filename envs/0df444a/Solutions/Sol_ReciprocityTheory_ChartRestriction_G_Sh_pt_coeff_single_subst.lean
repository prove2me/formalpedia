-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_coeff_single_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:35:20.913628+00:00
-- url     : https://prove2.me/submissions/50334032-8509-4dc5-a96d-944915697a63

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_degree_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
section Int
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
end Int
section Lin
variable {R : Type*} [CommRing R]
private theorem vmul_lemma {ρ K : Type*} [CommRing K] {P Q : MvPowerSeries ρ K} {m n : ℕ}
    (hP : ∀ e : ρ →₀ ℕ, e.degree < m → coeff e P = 0)
    (hQ : ∀ e : ρ →₀ ℕ, e.degree < n → coeff e Q = 0) :
    ∀ e : ρ →₀ ℕ, e.degree < m + n → coeff e (P * Q) = 0 := by
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree := by
    first
    | exact Finsupp.degree_add _ _
    | exact map_add _ _ _
  rw [hx'] at hdeg
  by_cases h1 : x.1.degree < m
  · rw [hP _ h1, zero_mul]
  · rw [hQ _ (by omega), mul_zero]
private theorem vzero_lemma_2 {ρ : Type*} {e : ρ →₀ ℕ} (h : e.degree = 0) : e = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff _).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h
private theorem vpow_lemma_3 {ρ K : Type*} [CommRing K] {A : MvPowerSeries ρ K}
    (hA : constantCoeff A = 0) (k : ℕ) :
    ∀ e : ρ →₀ ℕ, e.degree < k → coeff e (A ^ k) = 0 := by
  induction k with
  | zero => intro e he; omega
  | succ k ih =>
    rw [pow_succ]
    refine vmul_lemma ih ?_
    intro e he
    have h0 : e = 0 := vzero_lemma_2 (by omega)
    rw [h0, coeff_zero_eq_constantCoeff_apply, hA]
private theorem vprod_lemma_4 {ι ρ K : Type*} [CommRing K] {A : ι → MvPowerSeries ρ K}
    (hA : ∀ s, constantCoeff (A s) = 0) (d : ι →₀ ℕ) (T : Finset ι) :
    ∀ e : ρ →₀ ℕ, e.degree < ∑ s ∈ T, d s → coeff e (∏ s ∈ T, A s ^ d s) = 0 := by
  classical
  refine Finset.induction_on T (fun e he => by simp at he) (fun a T ha ih => ?_)
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact vmul_lemma (vpow_lemma_3 (hA a) (d a)) ih
end Lin
section Law
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
end Law
end
end ReciprocityTheory.ChartRestriction.G.Sh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {σ τ : Type*} [Fintype σ]
    {A : σ → MvPowerSeries τ R} (hA : HasSubst A) (hA0 : ∀ s, constantCoeff (A s) = 0)
    {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) (i : τ) :
    coeff (Finsupp.single i 1) (subst A f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single i 1) (A s) := by
  classical
  rw [MvPowerSeries.coeff_subst hA f (Finsupp.single i 1)]
  have hi1 : (Finsupp.single i 1 : τ →₀ ℕ).degree = 1 := by
    first
    | exact Finsupp.degree_single i 1
    | simp [Finsupp.degree]
  have hsupp : (Function.support fun d : σ →₀ ℕ =>
      coeff d f • coeff (Finsupp.single i 1) (d.prod fun s e => A s ^ e)) ⊆
      ↑(Finset.univ.image fun s : σ => Finsupp.single s 1) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    by_contra hns
    apply hd
    by_cases hd0 : d = 0
    · rw [hd0, coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · have hdeg : 2 ≤ d.degree := by
        by_contra hlt
        have hne : d.degree ≠ 0 := fun h0 => hd0 (vzero_lemma_2 h0)
        have h1 : d.degree = 1 := by omega
        obtain ⟨s, hs⟩ := pt_degree_eq_one h1
        apply hns
        rw [hs]
        exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ s))
      have hlt : (Finsupp.single i 1 : τ →₀ ℕ).degree < d.degree := by omega
      have hz : coeff (Finsupp.single i 1) (d.prod fun s e => A s ^ e) = 0 :=
        vprod_lemma_4 hA0 d d.support _ hlt
      rw [hz, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.prod_single_index (by simp)]
    simp only [pow_one, smul_eq_mul]
  · intro s _ t _ hst
    exact (Finsupp.single_left_inj one_ne_zero).mp hst
end ReciprocityTheory.ChartRestriction.G.Sh
