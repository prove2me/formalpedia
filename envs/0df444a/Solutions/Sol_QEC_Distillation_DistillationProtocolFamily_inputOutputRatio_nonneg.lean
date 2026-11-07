-- Prove2me | solution 1 for QEC.Distillation.DistillationProtocolFamily.inputOutputRatio_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:58:48.696842+00:00
-- url     : https://prove2.me/submissions/41016181-285b-4162-98d9-ba39fdd9d118

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead

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
    0 ≤ family.inputOutputRatio index := by
  exact div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (Nat.cast_pos.mpr (family.outputResourceCount_pos index)))
end QEC.Distillation.DistillationProtocolFamily
