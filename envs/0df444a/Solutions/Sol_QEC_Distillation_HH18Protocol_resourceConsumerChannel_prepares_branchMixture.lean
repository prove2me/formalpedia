-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.resourceConsumerChannel_prepares_branchMixture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:21:21.078295+00:00
-- url     : https://prove2.me/submissions/43229864-3e1a-4059-ade2-e0cd8ff4f2ca

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceDiagonal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceChannel
import Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchState_normSq
import Theorems.Thm_QEC_Distillation_HH18Protocol_prepareMeasuredResources_toOperator
import Theorems.Thm_QEC_Distillation_HH18Protocol_resourceConsumerChannel_errorWordBasisDensity
attribute [local simp] QEC.Distillation.HH18Protocol.prepareMeasuredResources_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
private theorem quantumChannel_apply_input_of_explicit_support
    {ι H K : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (channel : QuantumChannel H K) (input : Operator H) (weight : ι → Complex)
    (inputState : ι → DensityOperator H) (outputState : ι → DensityOperator K)
    (hinput : input = support.sum (fun i => weight i • (inputState i).toOperator))
    (hpointwise : ∀ i, channel (inputState i).toOperator = (outputState i).toOperator) :
    channel input = support.sum (fun i => weight i • (outputState i).toOperator) := by
  rw [hinput]
  change channel.toLinearMap
    (support.sum (fun i => weight i • (inputState i).toOperator)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, hpointwise i]
end HH18Protocol
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.HH18Protocol.instChannelClassicalDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (inputs : ResourceInput resourceCount QubitSpace) :
    resourceConsumerChannel (prepareMeasuredResources inputs).toOperator =
      physicalErrorWords.sum (fun error =>
        (measuredErrorWordProbability inputs error : Complex) •
          (DensityOperator.pureDensity (errorBranchState error)
            (errorBranchState_normSq error)).toOperator) := by
  exact quantumChannel_apply_input_of_explicit_support
    physicalErrorWords resourceConsumerChannel
    (prepareMeasuredResources inputs).toOperator
    (fun error => (measuredErrorWordProbability inputs error : Complex))
    errorWordBasisDensity
    (fun error => DensityOperator.pureDensity (errorBranchState error)
      (errorBranchState_normSq error))
    (prepareMeasuredResources_toOperator inputs)
    resourceConsumerChannel_errorWordBasisDensity
end QEC.Distillation.HH18Protocol
