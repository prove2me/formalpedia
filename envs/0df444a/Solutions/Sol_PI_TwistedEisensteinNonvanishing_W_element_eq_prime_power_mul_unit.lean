-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.element_eq_prime_power_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:59:10.308243+00:00
-- url     : https://prove2.me/submissions/0fa5dee8-181e-4ae0-bada-0c7c86b13c9b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iMul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open NTA
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution : ElementEqPrimePowerMulUnit := by
  intro E _ _ P hp hq a ha
  have hq0 := q_ne P hp
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨k, u, hu, hu0, hui, huii⟩ := decomp P hp hq hx0
  obtain ⟨k', u', hu', hu0', hui', huii'⟩ := decomp P hp hq hy0
  refine ⟨(k : ℤ) - k', u / u', ?_, div_ne_zero hu0 hu0', ?_, ?_⟩
  · rw [hu, hu', zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp
  · rw [div_eq_mul_inv]
    exact iMul P hui huii'
  · rw [inv_div, div_eq_mul_inv]
    exact iMul P hui' huii
end PI.TwistedEisensteinNonvanishing.W
