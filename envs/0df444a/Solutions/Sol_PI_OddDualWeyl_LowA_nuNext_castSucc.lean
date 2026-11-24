-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.nuNext_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:45.751212+00:00
-- url     : https://prove2.me/submissions/ad29bd23-fa46-468a-ad11-b2f1136e7368

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.LowA
theorem _root_.solution {m : ℕ} (ν : Fin (m + 1) → ℕ) (t : Fin m) : nuNext ν t.castSucc = ν t.succ := by
  have ht := t.isLt
  have h : (t.castSucc : Fin (m + 1)).val + 1 < m + 1 := by rw [Fin.val_castSucc]; omega
  unfold PI.OddDualWeyl.nuNext
  rw [dif_pos h]
  congr 1
end PI.OddDualWeyl.LowA
