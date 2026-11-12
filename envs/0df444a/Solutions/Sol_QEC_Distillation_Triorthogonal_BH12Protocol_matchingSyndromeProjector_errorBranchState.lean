-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.matchingSyndromeProjector_errorBranchState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:46:14.217485+00:00
-- url     : https://prove2.me/submissions/afeb74b7-c5f5-413d-8cc0-b755e7e03cfa

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_errorBranchState_xCheck_eigen
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution {q : Nat}
    (error : PhysicalError q) :
    jointStabilizerProjector (xChecks q) (xChecks_commute q)
        (syndromeOfError error) (errorBranchState error) =
      errorBranchState error := by
  apply (jointStabilizerProjector_fixed_iff
    (xChecks q) (xChecks_commute q) (syndromeOfError error)
      (errorBranchState error)).2
  exact errorBranchState_xCheck_eigen error
end QEC.Distillation.Triorthogonal.BH12Protocol
