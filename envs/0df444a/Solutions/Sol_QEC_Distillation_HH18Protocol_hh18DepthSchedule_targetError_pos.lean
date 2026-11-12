-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSchedule_targetError_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:46:15.671204+00:00
-- url     : https://prove2.me/submissions/e485a654-fee9-4129-95a5-bc973f6beafb

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18CubicErrorEnvelope_closed_form

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (depth : Nat) :
    0 < hh18DepthScheduleTargetError epsilon depth := by
  have hscaled : 0 < hh18IterationScale *
      hh18DepthScheduleTargetError epsilon depth := by
    rw [hh18CubicErrorEnvelope_closed_form]
    exact pow_pos (mul_pos hh18IterationScale_pos hepsilon) _
  rcases (mul_pos_iff.mp hscaled) with hpositive | hnegative
  · exact hpositive.2
  · exact False.elim ((not_lt_of_ge hh18IterationScale_pos.le) hnegative.1)
end QEC.Distillation.HH18Protocol
