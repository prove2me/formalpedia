-- Prove2me | solution 1 for PI.EF.PK.rectInt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:13.304466+00:00
-- url     : https://prove2.me/submissions/52635c80-f076-467d-92bf-9e77f063d95e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA

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
theorem _root_.solution (f : ℂ → ℂ) (a b c d : ℝ)
    (H : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) : rectInt f a b c d = 0 := by
  unfold rectInt
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, c⟩ ⟨b, d⟩ H
end PI.EF.PK
