-- Prove2me | solution 1 for QEC.Distillation.DistillationProtocolFamily.successfulOutputCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:17:13.016904+00:00
-- url     : https://prove2.me/submissions/2dff8898-6641-41d9-a986-2d42e5cd2f19

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
    0 ≤ family.successfulOutputCost index := by
  refine div_nonneg (Nat.cast_nonneg _) ?_
  exact mul_nonneg
    (le_of_lt (Nat.cast_pos.mpr (family.outputResourceCount_pos index)))
    (family.protocol index).run.success_nonneg
end QEC.Distillation.DistillationProtocolFamily
