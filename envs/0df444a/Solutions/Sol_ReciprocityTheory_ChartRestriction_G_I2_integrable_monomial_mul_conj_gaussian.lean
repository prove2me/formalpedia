-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integrable_monomial_mul_conj_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:14.105201+00:00
-- url     : https://prove2.me/submissions/9197cd63-2311-443f-83f9-7f4f8752a016

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_continuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_norm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_of_norm_le_gaussian

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
theorem _root_.solution {g : ℕ} (α β : Fin g →₀ ℕ) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) :=
    ((fa1Mono_continuous α).mul (Complex.continuous_conj.comp (fa1Mono_continuous β))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_norm.pow 2).neg))
  refine integrable_of_norm_le_gaussian hcont (∑ i, α i + ∑ i, β i) one_pos (C := 1) fun z => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), one_mul, neg_one_mul, pow_add]
  have h1 := fa1Mono_norm_le α z
  have h2 := fa1Mono_norm_le β z
  have he := (Real.exp_pos (-‖z‖ ^ 2)).le
  gcongr
end ReciprocityTheory.ChartRestriction.G.I2
