-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.resourceConsumerChannel_prepareMeasuredResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:02:19.23705+00:00
-- url     : https://prove2.me/submissions/aa79263f-b0a2-44b8-9df2-fc866e45ec83

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumerSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Theorems.Thm_QEC_Distillation_HH18Parameterized_resourceConsumerChannel_errorWordBasisDensity
import Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranchState_normSq
import Theorems.Thm_QEC_Distillation_HH18Parameterized_prepareMeasuredResources_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_quantumChannel_apply_input_of_explicit_support
attribute [local simp] QEC.Distillation.HH18Parameterized.prepareMeasuredResources_toOperator



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
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instConsumerClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instConsumerClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    resourceConsumerChannel h hdegree
      (prepareMeasuredResources m w inputs).toOperator =
      (physicalErrorWords m w).sum (fun error =>
        (measuredErrorWordProbability m w inputs error : Complex) •
          (DensityOperator.pureDensity (errorBranchState h hdegree error)
            (errorBranchState_normSq h hdegree error)).toOperator) := by
  apply quantumChannel_apply_input_of_explicit_support
    (physicalErrorWords m w) (resourceConsumerChannel h hdegree)
    (prepareMeasuredResources m w inputs)
    (fun error => (measuredErrorWordProbability m w inputs error : Complex))
    (errorWordBasisDensity m w)
    (fun error => DensityOperator.pureDensity (errorBranchState h hdegree error)
      (errorBranchState_normSq h hdegree error))
  · exact prepareMeasuredResources_toOperator m w inputs
  · intro error
    exact resourceConsumerChannel_errorWordBasisDensity h hdegree error
end QEC.Distillation.HH18Parameterized
