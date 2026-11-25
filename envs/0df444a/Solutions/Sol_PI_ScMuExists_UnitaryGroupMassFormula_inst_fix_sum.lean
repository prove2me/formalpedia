-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_fix_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:14.82233+00:00
-- url     : https://prove2.me/submissions/85bc4f44-ba7a-4781-bfe7-81c971ffaf82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstPlace
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
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (T : Finset (Fin n))
    (hm : ∀ i ∈ T, m *ᵥ Pi.single i 1 = Pi.single i 1) (c : Fin n → ℂ) (hc : ∀ i ∉ T, c i = 0) :
    m *ᵥ c = c := by
  have hc' : c = ∑ i ∈ T, c i • Pi.single i (1 : ℂ) := by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · exact hc r h
  rw [hc', Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.mulVec_smul, hm i hi]
end PI.ScMuExists.UnitaryGroupMassFormula
