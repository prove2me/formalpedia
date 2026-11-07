-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.quantumChannel_apply_input_of_explicit_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:30.04009+00:00
-- url     : https://prove2.me/submissions/6dd4d22e-ecf9-4c21-a4bd-99dba69ba715

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumerSupport

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Semantics
open scoped BigOperators
universe u
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
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
end QEC.Distillation.HH18Parameterized
