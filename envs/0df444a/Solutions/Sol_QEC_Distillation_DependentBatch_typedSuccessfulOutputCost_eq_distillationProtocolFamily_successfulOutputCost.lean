-- Prove2me | solution 1 for QEC.Distillation.DependentBatch.typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:19:36.987887+00:00
-- url     : https://prove2.me/submissions/51f97ac2-a6a7-4a63-9ab6-fcadf3d69a7a

import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_DependentBatch

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.DependentBatch
open Semantics
open scoped BigOperators
universe u v
namespace QEC.Distillation.DependentBatch
theorem _root_.solution
    {Resource Input Output Index : Type u}
    [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
    [FiniteQuantumSystem Resource]
    [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
    [FiniteQuantumSystem Input]
    [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
    [FiniteQuantumSystem Output]
    (family : DistillationProtocolFamily Resource Input Output Index) (index : Index)
    (InputSlots OutputSlots : Type*) [Fintype InputSlots] [Fintype OutputSlots]
    (yieldFactor : NNReal)
    (hinput : Fintype.card InputSlots = family.inputResourceCount index)
    (houtput : Fintype.card OutputSlots = family.outputResourceCount index)
    (hyield : (yieldFactor : ℝ) =
      (family.protocol index).run.successProbability) :
    typedSuccessfulOutputCost InputSlots OutputSlots yieldFactor =
      family.successfulOutputCost index := by
  unfold typedSuccessfulOutputCost typedInputOutputRatio
  rw [hinput, houtput, hyield, div_div]
  rfl
end QEC.Distillation.DependentBatch
