-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.chartRho_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:34.22779+00:00
-- url     : https://prove2.me/submissions/fba5c3da-ddf1-4d45-a62f-6d4c1e270879

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_weighted_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_of_mem_weighted
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartTheta_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartTheta_X_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
section Weight
variable [DecidableEq K]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end Weight
section Rho
variable {W : Ideal (MRingOver F ι)} [hWp : W.IsPrime]
private theorem aeval_mul_const_of_isMultiHomog {A : Type*} [CommRing A] [Algebra F A] (c : K → A)
    (y : (Σ k, ι k) → A) {f : MRingOver F ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    aeval (fun p => c p.1 * y p) f = (∏ k, c k ^ a k) * aeval y f := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).mp (mem_weighted_of_isMultiHomog hf)
    (MvPolynomial.mem_support_iff.mp hm)
  rw [weight_mw] at hw
  rw [aeval_monomial, aeval_monomial]
  have key : (m.prod fun p e => c p.1 ^ e) = ∏ k, c k ^ a k := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma, ← hw]
    simp only [Finset.prod_pow_eq_pow_sum]
  have split : (m.prod fun p e => (c p.1 * y p) ^ e) =
      (m.prod fun p e => c p.1 ^ e) * m.prod fun p e => y p ^ e := by
    simp only [mul_pow]
    exact Finsupp.prod_mul
  rw [split, key]
  ring
end Rho
section Point
variable {W : Ideal (MRingOver F ι)}
end Point
end ReciprocityTheory.ChartRestriction.G.AI.I1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {W : Ideal (MRingOver F ι)} [hWp : W.IsPrime]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution [DecidableEq K] {j : ∀ k, ι k} (hj : IsChart W j) {e : K → ℕ} {a : MRingOver F ι}
    (ha : a ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e) (h0 : chartRho W j a = 0) : a ∈ W := by
  have h1 := aeval_mul_const_of_isMultiHomog (chartC W j) (fun p => chartTheta W (X p))
    (isMultiHomog_of_mem_weighted ha)
  have h2 : aeval (fun p => chartTheta W (X p)) a = chartTheta W a :=
    (DFunLike.congr_fun (MvPolynomial.aeval_unique (chartTheta W)) a).symm
  have h3 : chartRho W j a = (∏ k, chartC W j k ^ e k) * chartTheta W a := by
    rw [← h2, ← h1]
    rfl
  rw [h3] at h0
  have hne : (∏ k, chartC W j k ^ e k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (chartTheta_X_ne_zero hj k))
  exact chartTheta_eq_zero_iff.mp ((mul_eq_zero.mp h0).resolve_left hne)
end ReciprocityTheory.ChartRestriction.G.AI.I1
