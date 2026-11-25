-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integral_monomial_mul_conj_gaussian_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:01.884121+00:00
-- url     : https://prove2.me/submissions/420519dd-0b95-47e1-a652-d8e3481abbbd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_rot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g : ℕ} {α β : Fin g →₀ ℕ} (h : α ≠ β) :
    ∫ z : EuclideanSpace ℂ (Fin g),
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hcon
    exact h (Finsupp.ext fun j => not_not.mp fun hne => hcon ⟨j, hne⟩)
  have hm : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  set u : Circle := Circle.exp (Real.pi / ((α j : ℝ) - β j)) with hu
  set F : EuclideanSpace ℂ (Fin g) → ℂ := fun z =>
    monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) with hF
  have hc : (u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j)) = -1 := by
    rw [hu, Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hm' : ((α j : ℂ) - β j) ≠ 0 := by exact_mod_cast hm
    have : (α j : ℂ) * (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) +
        (β j : ℂ) * (starRingEnd ℂ) (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) =
        Real.pi * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_pi_mul_I]
  have hrot : ∀ z, F (coordinateRotation j u z) =
      ((u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j))) * F z := by
    intro z
    simp only [hF, fa1Mono_rot, LinearIsometryEquiv.norm_map, map_mul]
    ring
  have hint : ∫ z, F (coordinateRotation j u z) = ∫ z, F z :=
    (coordinateRotation j u).measurePreserving.integral_comp (coordinateRotation j u).toHomeomorph.measurableEmbedding F
  simp_rw [hrot, hc] at hint
  rw [integral_const_mul] at hint
  linear_combination (-1 / 2 : ℂ) * hint
end ReciprocityTheory.ChartRestriction.G.I2
