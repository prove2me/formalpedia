-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.iteration_rate_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:32:55.189716+00:00
-- url     : https://prove2.me/submissions/d0ad319c-eafc-4361-9673-0e53b17cc983

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_iteration_rate_sum_with_tail_le

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
theorem _root_.solution (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    ∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1 ≤
      (4 / 3 : ℝ) * epsilon.1 := by
  calc
    ∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1 ≤
        (∑ stage : Fin depth, (hh18ErrorIteration epsilon hsmall stage.1).1) +
          (4 / 3 : ℝ) * (hh18ErrorIteration epsilon hsmall depth).1 := by
      exact le_add_of_nonneg_right
        (mul_nonneg (by norm_num) (hh18ErrorIteration epsilon hsmall depth).property.1)
    _ ≤ (4 / 3 : ℝ) * epsilon.1 :=
      iteration_rate_sum_with_tail_le epsilon hsmall depth
end QEC.Distillation.HH18Protocol
