-- Prove2me | solution 1 for PI.PolynomialProperness.CB.mx_of_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:48.78516+00:00
-- url     : https://prove2.me/submissions/c1fdad6f-3ac0-4652-8193-20463c4fad20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_GN_mx_le_iff


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
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c) : mx M ≤ c := (GN.mx_le_iff M hc).2 h
end PI.PolynomialProperness.CB
