-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.matchingSyndromeProjector_errorBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:21:10.425451+00:00
-- url     : https://prove2.me/submissions/a9849ced-24a7-4498-824a-11dd1188dd52

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranch_check_eigen
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff


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
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator w r m)
        (HH18PuncturedReedMuller.checkGenerator_commutes h)
        (measuredSyndrome w r m error)
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree)) =
      HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree) := by
  apply (jointStabilizerProjector_fixed_iff
    (HH18PuncturedReedMuller.checkGenerator w r m)
    (HH18PuncturedReedMuller.checkGenerator_commutes h)
    (measuredSyndrome w r m error)
    (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))).2
  exact errorBranch_check_eigen h hdegree error
end QEC.Distillation.HH18Parameterized
