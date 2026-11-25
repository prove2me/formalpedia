-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.hJ_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:25:24.198697+00:00
-- url     : https://prove2.me/submissions/36be9cd6-cda7-4797-9124-0bd4eec332cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
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
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, y i) = ∑ i ∈ s, hJ ε x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add, ih]
end PI.NMeasInv.UnitaryGroupMassFormula
