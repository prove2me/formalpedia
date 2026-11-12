-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathStageRun_success_one_sub_physicalInputCount_rate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:46:11.958853+00:00
-- url     : https://prove2.me/submissions/9dce8588-1d10-45bc-b9e7-f6a101000d87

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_allZeroWord_le
import Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_eq_acceptedBernoulliMass


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    1 - (physicalInputCount m w : ℝ) *
        (routedDepthPathRate h hdegree epsilon hsmall stage.1
          (routedDepthPathStagePath m w depth path stage)).1 ≤
      (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by
  let rate := routedDepthPathRate h hdegree epsilon hsmall stage.1
    (routedDepthPathStagePath m w depth path stage)
  change 1 - (physicalInputCount m w : ℝ) * rate.1 ≤
    endpointWeight h hdegree (noisyResources m w rate) .accepted
  have hrate : 0 ≤ rate.1 := rate.property.1
  calc
    1 - (physicalInputCount m w : ℝ) * rate.1 ≤
        (1 - rate.1) ^ physicalInputCount m w := by
      have hbernoulli := one_add_mul_sub_le_pow
        (a := 1 - rate.1) (by linarith [rate.property.2]) (physicalInputCount m w)
      calc
        1 - (physicalInputCount m w : ℝ) * rate.1 =
            1 + (physicalInputCount m w : ℝ) * ((1 - rate.1) - 1) := by ring
        _ ≤ (1 - rate.1) ^ physicalInputCount m w := hbernoulli
    _ ≤ acceptedBernoulliMass w r m rate :=
      acceptedBernoulliMass_allZeroWord_le h rate
    _ = endpointWeight h hdegree (noisyResources m w rate) .accepted :=
      (endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree rate).symm
end QEC.Distillation.HH18Parameterized
