-- Prove2me | solution 1 for PI.Dv.TIW.unzero_toAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:13.220281+00:00
-- url     : https://prove2.me/submissions/a7963b37-b6a7-47b0-a83b-1e89eecd526a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
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
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero
namespace PI.Dv.TIW
theorem _root_.solution (m : ℤᵐ⁰) (h : m ≠ 0) : Multiplicative.toAdd (WithZero.unzero h) = WithZero.log m := by
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
  first
  | rfl
  | simp [WithZero.log]
  | simp
end PI.Dv.TIW
