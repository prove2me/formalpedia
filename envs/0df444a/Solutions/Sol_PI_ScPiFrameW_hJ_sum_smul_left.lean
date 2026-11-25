-- Prove2me | solution 1 for PI.ScPiFrameW.hJ_sum_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:54.549867+00:00
-- url     : https://prove2.me/submissions/4b481573-ce65-4edf-bf27-755fca95a34a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
import Theorems.Thm_PI_ScPiFrameW_hJ_eq_sum
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}
namespace PI.ScPiFrameW
theorem _root_.solution (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (m : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a, g a • m a) y = ∑ a, star (g a) * hJ ε (m a) y := by
  simp only [hJ_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul',
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring
end PI.ScPiFrameW
