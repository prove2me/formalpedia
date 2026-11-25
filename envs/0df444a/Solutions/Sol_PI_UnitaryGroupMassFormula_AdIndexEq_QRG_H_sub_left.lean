-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:21.117927+00:00
-- url     : https://prove2.me/submissions/67080227-ad0c-4c46-8937-da53f496d6df

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_neg_left

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
theorem _root_.solution (x y z : Fin n → K) : H σ J (x - y) z = H σ J x z - H σ J y z := by
  rw [sub_eq_add_neg, H_add_left, H_neg_left, ← sub_eq_add_neg]
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
