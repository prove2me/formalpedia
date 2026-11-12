-- Prove2me | solution 1 for QEC.Distillation.HH18SyndromeDecoding.matchingSyndromeProjector_errorBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:53:27.501195+00:00
-- url     : https://prove2.me/submissions/8e113783-5e1b-4049-96ac-95e1bf819691

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_errorBranch_check_eigen
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff


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
theorem _root_.solution
    (error : PhysicalErrorWord) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator 0 1 4)
        (HH18PuncturedReedMuller.checkGenerator_commutes
          HH18NoisyInput.hh18_15_1_0_admissible)
        (measuredSyndrome error)
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch error) =
      HH18NoisyInput.hh18PhysicalTInvErrorBranch error := by
  apply (jointStabilizerProjector_fixed_iff
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)
    (measuredSyndrome error)
    (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)).2
  exact errorBranch_check_eigen error
end QEC.Distillation.HH18SyndromeDecoding
