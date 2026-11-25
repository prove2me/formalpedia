-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.Pw_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:07.346934+00:00
-- url     : https://prove2.me/submissions/84585978-1511-4211-8040-4733592e9817

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_add
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_zero
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
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : ι → Fin n → ℂ) :
    Pw ε e f (∑ i ∈ s, x i) = ∑ i ∈ s, Pw ε e f (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Pw_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Pw_add, ih]
end PI.NMeasInv.UnitaryGroupMassFormula
