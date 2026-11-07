-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.linearMap_apply_input_of_explicit_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:34.285147+00:00
-- url     : https://prove2.me/submissions/6f0a776b-04f0-4b50-9773-00a6461a40ff

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport

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
    (linearMap : Operator H →ₗ[Complex] Operator K) (input : Operator H)
    (weight : ι → Complex) (inputSummand : ι → Operator H)
    (outputSummand : ι → Operator K)
    (hinput : input = support.sum (fun i => weight i • inputSummand i))
    (hpointwise : ∀ i, linearMap (inputSummand i) = outputSummand i) :
    linearMap input = support.sum (fun i => weight i • outputSummand i) := by
  rw [hinput, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, hpointwise i]
end QEC.Distillation.HH18Parameterized
