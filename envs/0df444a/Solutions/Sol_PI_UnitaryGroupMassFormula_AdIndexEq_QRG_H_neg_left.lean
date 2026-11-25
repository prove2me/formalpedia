-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:59.742526+00:00
-- url     : https://prove2.me/submissions/7bfd5c54-59c2-4cfa-b820-0f7bc7fbf178

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_comp_neg__f00b25033542

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (x y : Fin n → K) : H σ J (-x) y = - H σ J x y := by
  unfold H
  rw [comp_neg' σ, neg_dotProduct]
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
