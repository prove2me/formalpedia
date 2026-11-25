-- Prove2me | solution 1 for PI.EF.PK.seg_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:55.27614+00:00
-- url     : https://prove2.me/submissions/2d518e8b-edc0-40a9-9e32-0784d06c608c

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
theorem _root_.solution (f : ℝ → ℂ) (K a b : ℝ) (hab : a ≤ b) (h : ∀ x, a ≤ x → x ≤ b → ‖f x‖ ≤ K) :
    ‖∫ x in a..b, f x‖ ≤ K * (b - a) := by
  have hK := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (C := K) (a := a) (b := b)
    (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      exact h x hx.1.le hx.2)
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at hK
end PI.EF.PK
