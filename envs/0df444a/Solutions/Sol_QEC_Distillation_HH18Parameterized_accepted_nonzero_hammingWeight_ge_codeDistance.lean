-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.accepted_nonzero_hammingWeight_ge_codeDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:25:56.786207+00:00
-- url     : https://prove2.me/submissions/aac333ae-0033-4bf3-956c-d7152e03162d

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedError_eq_zero_of_hammingWeight_lt_codeDistance

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
universe u
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (herror : error ≠ 0) (haccept : Accepts w r m error) :
    codeDistance r w ≤ HammingWeight error := by
  by_contra hlt
  have hweight : HammingWeight error < codeDistance r w := by omega
  exact herror
    (acceptedError_eq_zero_of_hammingWeight_lt_codeDistance h error hweight haccept)
end QEC.Distillation.HH18Parameterized
