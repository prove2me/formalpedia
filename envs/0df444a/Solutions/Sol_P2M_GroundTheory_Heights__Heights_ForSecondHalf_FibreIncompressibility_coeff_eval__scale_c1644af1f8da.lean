-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_coeff_eval__scale_c1644af1f8da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:08.966611+00:00
-- url     : https://prove2.me/submissions/0c240dd6-6be6-4e0d-be30-ba0957371ecf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncompTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
variable {S : Type} [CommRing S]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
theorem _root_.solution {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A] (f : R →+* A) (b : σ → A)
    (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (eval₂ ((C : A →+* MvPolynomial σ A).comp f) (fun k => X k * C (b k)) P) =
      f (coeff m P) * ∏ k, b k ^ m k := by
  classical
  have hterm : ∀ d : σ →₀ ℕ, ((C : A →+* MvPolynomial σ A).comp f) (coeff d P) *
      ∏ k, (X k * C (b k)) ^ d k = monomial d (f (coeff d P) * ∏ k, b k ^ d k) := by
    intro d
    have hX : ∏ k, (X k : MvPolynomial σ A) ^ d k = monomial d 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hC : ∏ k, (C (b k) : MvPolynomial σ A) ^ d k = C (∏ k, b k ^ d k) := by
      simp only [map_prod, map_pow]
    rw [RingHom.comp_apply]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, hX, hC, mul_comm (monomial d 1), ← mul_assoc, ← C_mul, C_mul_monomial, mul_one]
  rw [eval₂_eq']
  simp_rw [hterm, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
