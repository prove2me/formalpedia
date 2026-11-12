-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.acceptedNonzeroErrorWordWeight_le_codeDistance_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:04:59.968123+00:00
-- url     : https://prove2.me/submissions/0d476241-4012-4bc0-bb36-de12cf888925

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Theorems.Thm_QEC_Distillation_HH18Parameterized_errorWordWeight_le_codeDistance_pow_of_hammingWeight_ge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_accepted_nonzero_hammingWeight_ge_codeDistance


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
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (error : PhysicalErrorWord m w)
    (hresidual : Accepts w r m error ∧ error ≠ 0) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ codeDistance r w :=
  errorWordWeight_le_codeDistance_pow_of_hammingWeight_ge epsilon error
    (accepted_nonzero_hammingWeight_ge_codeDistance h error hresidual.2 hresidual.1)
end QEC.Distillation.HH18Parameterized
