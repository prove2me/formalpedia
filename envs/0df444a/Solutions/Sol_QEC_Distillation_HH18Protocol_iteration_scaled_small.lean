-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.iteration_scaled_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:43:10.945203+00:00
-- url     : https://prove2.me/submissions/14fd5fa1-480b-4a10-a8d6-b0a74840eca2

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18CubicErrorEnvelope_closed_form
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18ErrorIteration_le_cubicEnvelope

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
    hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1 ≤ 1 / 2 := by
  have hscale : 0 ≤ hh18IterationScale := hh18IterationScale_pos.le
  have hrate : 0 ≤ (hh18ErrorIteration epsilon hsmall depth).1 :=
    (hh18ErrorIteration epsilon hsmall depth).property.1
  have henvelope := hh18ErrorIteration_le_cubicEnvelope epsilon hsmall depth
  have hbase : 0 ≤ hh18IterationScale * epsilon.1 :=
    mul_nonneg hscale epsilon.property.1
  calc
    hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1 ≤
        hh18IterationScale * hh18CubicErrorEnvelope epsilon depth :=
      mul_le_mul_of_nonneg_left henvelope hscale
    _ = (hh18IterationScale * epsilon.1) ^ (3 ^ depth) :=
      hh18CubicErrorEnvelope_closed_form epsilon depth
    _ ≤ (1 / 2 : ℝ) ^ (3 ^ depth) :=
      pow_le_pow_left₀ hbase hsmall _
    _ ≤ (1 / 2 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (m := 1) (n := 3 ^ depth)
        (by norm_num) (by norm_num)
        (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3))
    _ = (1 / 2 : ℝ) := by norm_num
end QEC.Distillation.HH18Protocol
