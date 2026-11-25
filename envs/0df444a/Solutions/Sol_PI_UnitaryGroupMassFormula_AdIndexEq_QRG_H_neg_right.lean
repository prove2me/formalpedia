-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:36.54138+00:00
-- url     : https://prove2.me/submissions/7d7568be-ddab-46ed-8ca3-1745637b9c29

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen

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
theorem _root_.solution (x y : Fin n → K) : H σ J x (-y) = - H σ J x y := by
  simp [H, Matrix.mulVec_neg, dotProduct_neg]
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
