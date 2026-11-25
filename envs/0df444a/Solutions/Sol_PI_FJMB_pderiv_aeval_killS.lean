-- Prove2me | solution 1 for PI.FJMB.pderiv_aeval_killS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:42.774882+00:00
-- url     : https://prove2.me/submissions/4487b376-7bbb-4269-b573-dafc9caf3864

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Theorems.Thm_PI_FJMB_deriv_aeval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution (S : Set σ) (w : σ) (hw : w ∉ S) (f : MvPolynomial σ ℂ) :
    pderiv w (aeval (killS S) f) = aeval (killS S) (pderiv w f) := by
  have h := deriv_aeval (R := ℂ) (pderiv w) (killS S) {w} (fun v hv => by
    have hv' : v ≠ w := by simpa using hv
    by_cases h : v ∈ S <;> simp [killS, h, pderiv_X_of_ne hv']) f
  rw [h]
  simp [killS, hw]
end PI.FJMB
