-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_one_eq_oneLevelProtocolFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:35:02.798199+00:00
-- url     : https://prove2.me/submissions/8fe67ede-0e84-4234-a048-d2cdfe5e60e1

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_oneLevelSuccessfulOutputCost_eq_oneLevelProtocolFamily
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSuccessfulOutputCost_one_eq_oneLevelSuccessfulOutputCost

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    hh18DepthSuccessfulOutputCost epsilon hsmall 1 =
      (hh18OneLevelProtocolFamily epsilon).successfulOutputCost PUnit.unit := by
  calc
    hh18DepthSuccessfulOutputCost epsilon hsmall 1 =
        oneLevelSuccessfulOutputCost epsilon :=
      hh18DepthSuccessfulOutputCost_one_eq_oneLevelSuccessfulOutputCost epsilon hsmall
    _ = (hh18OneLevelProtocolFamily epsilon).successfulOutputCost PUnit.unit :=
      oneLevelSuccessfulOutputCost_eq_oneLevelProtocolFamily epsilon
end QEC.Distillation.HH18Protocol
