-- Prove2me | solution 1 for PI.PolynomialProperness.CB.kap_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:20.337901+00:00
-- url     : https://prove2.me/submissions/5b08a5d0-5ce4-43c1-86f0-2b2d0f09de3e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_GN_mx_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : 1 ≤ kap m P := by
  unfold kap; have := GN.mx_nonneg P⁻¹; have : (0 : ℝ) ≤ m := by positivity
  nlinarith
end PI.PolynomialProperness.CB
