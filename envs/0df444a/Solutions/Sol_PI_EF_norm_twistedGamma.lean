-- Prove2me | solution 1 for PI.EF.norm_twistedGamma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:36.869435+00:00
-- url     : https://prove2.me/submissions/d57181d1-2955-4497-a0bb-9327cc541473

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Set
namespace PI.EF
theorem _root_.solution (w : ℂ) :
    ‖frobeniusStickelbergerDetMulSigmaCube w‖ = ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im) / ‖w + 1‖ ^ 5 := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [norm_div, norm_mul, norm_pow, Complex.norm_exp]
  congr 3
  simp
end PI.EF
