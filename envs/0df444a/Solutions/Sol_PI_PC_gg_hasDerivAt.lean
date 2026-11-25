-- Prove2me | solution 1 for PI.PC.gg_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:10.851213+00:00
-- url     : https://prove2.me/submissions/ae884978-2a9a-476f-96f0-e31896c26c4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution {t : ℝ} (ht : 1 < t) : HasDerivAt gg (gg' t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (Real.log_pos ht).ne'
  have hL : HasDerivAt log t⁻¹ t := Real.hasDerivAt_log ht0
  have hsq := hL.mul hL
  have hq := (hasDerivAt_id' t).div hsq (mul_ne_zero hl hl)
  have h := (hq.const_mul (1.56 : ℝ)).add (hL.const_mul (0.7 : ℝ))
  have hfun : gg = fun y => 1.56 * (y / (log y * log y)) + 0.7 * log y := by
    funext y; simp only [gg]; ring
  have hd : 1.56 * ((1 * (log t * log t) - t * (t⁻¹ * log t + log t * t⁻¹)) / (log t * log t) ^ 2)
      + 0.7 * t⁻¹ = gg' t := by
    show _ = 1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t
    first | (field_simp; ring) | field_simp
  rw [hfun]
  exact h.congr_deriv hd
end PI.PC
