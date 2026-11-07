-- Prove2me | solution 1 for QEC.Distillation.DistillationProtocolFamily.successfulOutputCost_denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:17:14.27517+00:00
-- url     : https://prove2.me/submissions/918cf06e-cdc5-47c3-8292-039281ad53be

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
    (index : Index)
    (hsuccess : 0 < (family.protocol index).run.successProbability) :
    0 < (family.outputResourceCount index : ℝ) *
      (family.protocol index).run.successProbability := by
  exact mul_pos
    (Nat.cast_pos.mpr (family.outputResourceCount_pos index)) hsuccess
end QEC.Distillation.DistillationProtocolFamily
