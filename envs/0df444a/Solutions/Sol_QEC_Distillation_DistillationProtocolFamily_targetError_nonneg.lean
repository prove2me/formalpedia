-- Prove2me | solution 1 for QEC.Distillation.DistillationProtocolFamily.targetError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:16:49.962576+00:00
-- url     : https://prove2.me/submissions/83b566fa-a1ed-43a7-bf9c-ee532c59ca64

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
import Theorems.Thm_QEC_Distillation_MagicStateDistillationProtocol_successfulOutputError_nonneg


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
    (index : Index) :
    0 ≤ family.targetError index := by
  calc
    0 ≤ (family.protocol index).successfulOutputError :=
      (family.protocol index).successfulOutputError_nonneg
    _ ≤ family.targetError index :=
      family.successfulOutputError_le_targetError index
end QEC.Distillation.DistillationProtocolFamily
