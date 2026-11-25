-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.valuation_exponent_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:52.685305+00:00
-- url     : https://prove2.me/submissions/ce0ff435-a847-4835-83ba-51cbad5c7002

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_no_shift

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
theorem _root_.solution : ValuationExponentUnique := by
  intro E _ _ P hp hq e e' w w' hw hwi hwii hw'i hw'ii h
  have hq0 := q_ne P hp
  have hw' : w' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hw ((mul_eq_zero.mp h).resolve_left (zpow_ne_zero _ hq0))
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e' - e = (d : ℤ) + 1 := ⟨(e' - e - 1).toNat, by omega⟩
    apply no_shift P hp d hw hwii hw'i
    have hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e' - e) := by
      rw [hd, ← Nat.cast_succ, zpow_natCast]
    rw [hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]
    linear_combination h
  · exact heq
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e - e' = (d : ℤ) + 1 := ⟨(e - e' - 1).toNat, by omega⟩
    apply no_shift P hp d hw' hw'ii hwi
    have hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e - e') := by
      rw [hd, ← Nat.cast_succ, zpow_natCast]
    rw [hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]
    linear_combination -h
end PI.TwistedEisensteinNonvanishing.W
