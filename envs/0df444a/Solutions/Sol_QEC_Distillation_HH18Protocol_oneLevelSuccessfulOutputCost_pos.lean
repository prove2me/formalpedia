-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.oneLevelSuccessfulOutputCost_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:33:13.208768+00:00
-- url     : https://prove2.me/submissions/a5782f2d-fdb9-4adc-98bc-0fe52bc83f4a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_oneLevelSuccessfulOutputCost_eq_fifteen_div_success
import Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_pos


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
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < oneLevelSuccessfulOutputCost epsilon := by
  rw [oneLevelSuccessfulOutputCost_eq_fifteen_div_success]
  exact div_pos (by norm_num) (endpointWeight_accepted_pos epsilon)
end QEC.Distillation.HH18Protocol
