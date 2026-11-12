-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.iteration_next_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:27:10.496412+00:00
-- url     : https://prove2.me/submissions/78b01a65-8c5b-4168-b2d1-99975d19005d

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_iteration_scaled_small

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
    (hh18ErrorIteration epsilon hsmall (depth + 1)).1 ≤
      (hh18ErrorIteration epsilon hsmall depth).1 / 4 := by
  have hrate : 0 ≤ (hh18ErrorIteration epsilon hsmall depth).1 :=
    (hh18ErrorIteration epsilon hsmall depth).property.1
  have hscaled := iteration_scaled_small epsilon hsmall depth
  have hscale_sq :
      (hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1) ^ 2 ≤
        (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_left₀
      (mul_nonneg hh18IterationScale_pos.le hrate) hscaled 2
  have hnextsmall :
      hh18NextInputSmallDomain (hh18ErrorIteration epsilon hsmall depth) := by
    unfold hh18NextInputSmallDomain
    calc
      (2 * residualCubicCoefficient) *
          (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 ≤
          hh18IterationScale ^ 2 *
            (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
        mul_le_mul_of_nonneg_right
          two_mul_residualCubicCoefficient_le_iterationScale_sq (pow_nonneg hrate 3)
      _ = (hh18ErrorIteration epsilon hsmall depth).1 *
            (hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1) ^ 2 := by
        ring
      _ ≤ (hh18ErrorIteration epsilon hsmall depth).1 * (1 / 2 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hscale_sq hrate
      _ ≤ 1 / 2 := by
        nlinarith [(hh18ErrorIteration epsilon hsmall depth).property.2]
  change (hh18NextInputErrorRate (hh18ErrorIteration epsilon hsmall depth) hnextsmall).1 ≤ _
  calc
    (hh18NextInputErrorRate (hh18ErrorIteration epsilon hsmall depth) hnextsmall).1 ≤
        (2 * residualCubicCoefficient) *
          (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
      hh18NextInputErrorRate_le_cubic _ hnextsmall
    _ ≤ hh18IterationScale ^ 2 *
          (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
      mul_le_mul_of_nonneg_right
        two_mul_residualCubicCoefficient_le_iterationScale_sq (pow_nonneg hrate 3)
    _ = (hh18ErrorIteration epsilon hsmall depth).1 *
          (hh18IterationScale * (hh18ErrorIteration epsilon hsmall depth).1) ^ 2 := by
      ring
    _ ≤ (hh18ErrorIteration epsilon hsmall depth).1 * (1 / 2 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hscale_sq hrate
    _ = (hh18ErrorIteration epsilon hsmall depth).1 / 4 := by ring
end QEC.Distillation.HH18Protocol
