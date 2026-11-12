-- Prove2me | solution 1 for QEC.Distillation.HH18SyndromeDecoding.accepted_nonzero_hammingWeight_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:47:56.545895+00:00
-- url     : https://prove2.me/submissions/f0ab6a0e-b90f-4041-bd05-56ebec747987

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SyndromeDecoding
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18SyndromeDecoding
theorem _root_.solution (error : PhysicalErrorWord)
    (herror : error ≠ 0) (haccept : Accepts error) :
    3 ≤ HammingWeight error := by
  by_contra hlt
  have hweight : HammingWeight error < 3 := by omega
  exact herror (acceptedError_eq_zero_of_hammingWeight_lt_three error hweight haccept)
end QEC.Distillation.HH18SyndromeDecoding
