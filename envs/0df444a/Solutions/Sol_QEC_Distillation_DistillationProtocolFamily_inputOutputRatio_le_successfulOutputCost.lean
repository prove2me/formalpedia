-- Prove2me | solution 1 for QEC.Distillation.DistillationProtocolFamily.inputOutputRatio_le_successfulOutputCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:17:18.761009+00:00
-- url     : https://prove2.me/submissions/67ce2613-e7cc-42d1-a722-95e5578db40a

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
import Theorems.Thm_QEC_Distillation_DistillationProtocolFamily_inputOutputRatio_nonneg
import Theorems.Thm_QEC_Distillation_DistillationProtocolFamily_successfulOutputCost_eq_inputOutputRatio_div_successProbability

set_option autoImplicit false
universe u
open QEC QEC.Distillation
open Semantics
open QEC.Distillation.DistillationProtocolFamily
variable {Resource Input Output Index : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
namespace QEC.Distillation.DistillationProtocolFamily
theorem _root_.solution
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index)
    (hsuccess : 0 < (family.protocol index).run.successProbability) :
    family.inputOutputRatio index ≤ family.successfulOutputCost index := by
  rw [family.successfulOutputCost_eq_inputOutputRatio_div_successProbability index]
  exact (le_div_iff₀ hsuccess).2
    (mul_le_of_le_one_right (family.inputOutputRatio_nonneg index)
      (family.protocol index).run.success_le_one)
end QEC.Distillation.DistillationProtocolFamily
