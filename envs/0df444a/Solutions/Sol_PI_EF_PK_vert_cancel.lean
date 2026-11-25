-- Prove2me | solution 1 for PI.EF.PK.vert_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:03.092066+00:00
-- url     : https://prove2.me/submissions/c9c9756e-a360-4a73-a19d-7b9401539d42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (G k : ℝ → ℂ) (T' : ℝ) :
    2 * π * I * ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in -T'..T', -G t * k t) =
      -(I * ∫ t : ℝ in -T'..T', G t * k t) := by
  have h : ∫ t : ℝ in -T'..T', -G t * k t = -∫ t : ℝ in -T'..T', G t * k t := by
    simp only [neg_mul]
    exact intervalIntegral.integral_neg
  rw [h]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
end PI.EF.PK
