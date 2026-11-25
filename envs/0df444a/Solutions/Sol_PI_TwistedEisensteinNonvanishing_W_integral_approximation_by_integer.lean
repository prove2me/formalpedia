-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.integral_approximation_by_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:22.796202+00:00
-- url     : https://prove2.me/submissions/2f189f9b-156c-4cc0-9371-50eee4d76d6f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_approx1

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
theorem _root_.solution : IntegralApproximationByInteger := by
  intro E _ _ P hp hq x N hx
  have hq0 := q_ne P hp
  induction N with
  | zero => exact ⟨0, by simp, by simpa using hx⟩
  | succ N ih =>
    obtain ⟨i, hi, hz⟩ := ih
    obtain ⟨d, hd, hzd⟩ := approx1 P hp hq hz
    refine ⟨i + d * qOf P ^ N, ?_, ?_⟩
    · calc i + d * qOf P ^ N < qOf P ^ N + d * qOf P ^ N := Nat.add_lt_add_right hi _
        _ = (d + 1) * qOf P ^ N := by ring
        _ ≤ qOf P * qOf P ^ N := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hd)
        _ = qOf P ^ (N + 1) := by ring
    · have e : (x - ((i + d * qOf P ^ N : ℕ) : E)) / (qOf P : E) ^ (N + 1) =
          ((x - i) / (qOf P : E) ^ N - d) / (qOf P : E) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact hzd
end PI.TwistedEisensteinNonvanishing.W
