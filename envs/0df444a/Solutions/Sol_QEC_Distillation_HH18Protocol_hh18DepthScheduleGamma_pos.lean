-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthScheduleGamma_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:32:26.247433+00:00
-- url     : https://prove2.me/submissions/91775207-0e46-4679-b802-8ef216020216

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol

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
theorem _root_.solution : 0 < hh18DepthScheduleGamma := by
  unfold hh18DepthScheduleGamma
  exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 15))
    (Real.log_pos (by norm_num : (1 : ℝ) < 3))
end QEC.Distillation.HH18Protocol
