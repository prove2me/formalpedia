-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:11:57.515338+00:00
-- url     : https://prove2.me/submissions/09ccede4-669d-44fb-8b0a-2cb0fa1f22ff

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decoderChannel_zeroErrorBranch_eq_ideal
import Theorems.Thm_QEC_Distillation_HH18Parameterized_centered_sum_of_explicit_support
import Theorems.Thm_QEC_Distillation_HH18Parameterized_complex_of_real_sum_of_explicit_support
import Theorems.Thm_QEC_Distillation_HH18Parameterized_linearMap_apply_selected_sum_of_explicit_support
import Theorems.Thm_QEC_Distillation_HH18Parameterized_rawAcceptedEndpoint_noisyResources_eq_errorWordSum

section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
private theorem rawAcceptedEndpoint_eq_physicalErrorWords {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint h hdegree (noisyResources m w epsilon) .accepted =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            errorBranchOperator h hdegree error
        else 0) :=
  rawAcceptedEndpoint_noisyResources_eq_errorWordSum h hdegree epsilon
private theorem acceptedBernoulliMass_eq_physicalErrorWords (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedBernoulliMass w r m epsilon =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then HH18NoisyInput.errorWordWeight epsilon error else 0) :=
  rfl
private theorem acceptedBernoulliMass_cast_eq_physicalErrorWords (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (acceptedBernoulliMass w r m epsilon : Complex) =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex)
        else 0) := by
  exact complex_of_real_sum_of_explicit_support
    (physicalErrorWords m w)
    (acceptedBernoulliMass w r m epsilon)
    (HH18NoisyInput.errorWordWeight epsilon)
    (Accepts w r m)
    (acceptedBernoulliMass_eq_physicalErrorWords w r m epsilon)
private theorem decodedRawAcceptedEndpoint_eq_physicalErrorWords {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted) =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            decoderChannel h (errorBranchOperator h hdegree error)
        else 0) := by
  exact linearMap_apply_selected_sum_of_explicit_support
    (physicalErrorWords m w)
    (decoderChannel h).toLinearMap
    (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted)
    (fun error => (HH18NoisyInput.errorWordWeight epsilon error : Complex))
    (Accepts w r m)
    (errorBranchOperator h hdegree)
    (fun error => decoderChannel h (errorBranchOperator h hdegree error))
    (rawAcceptedEndpoint_eq_physicalErrorWords h hdegree epsilon)
    (fun error => rfl)
private theorem acceptedResidualDecodedDifference_eq_physicalErrorWords {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualDecodedDifference h hdegree epsilon =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error ∧ error ≠ 0 then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            (decoderChannel h (errorBranchOperator h hdegree error) -
              (idealLogicalTOutput m w).toOperator)
        else 0) :=
  rfl
end HH18Parameterized
end Distillation
end QEC
end
end

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
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted) -
        (acceptedBernoulliMass w r m epsilon : Complex) •
          (idealLogicalTOutput m w).toOperator =
      acceptedResidualDecodedDifference h hdegree epsilon := by
  exact centered_sum_of_explicit_support
    (physicalErrorWords m w)
    (fun error => (HH18NoisyInput.errorWordWeight epsilon error : Complex))
    (Accepts w r m)
    (fun error => decoderChannel h (errorBranchOperator h hdegree error))
    0
    (idealLogicalTOutput m w).toOperator
    (decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted))
    (acceptedResidualDecodedDifference h hdegree epsilon)
    (acceptedBernoulliMass w r m epsilon : Complex)
    (decodedRawAcceptedEndpoint_eq_physicalErrorWords h hdegree epsilon)
    (acceptedBernoulliMass_cast_eq_physicalErrorWords w r m epsilon)
    (acceptedResidualDecodedDifference_eq_physicalErrorWords h hdegree epsilon)
    (decoderChannel_zeroErrorBranch_eq_ideal h hdegree)
end QEC.Distillation.HH18Parameterized
