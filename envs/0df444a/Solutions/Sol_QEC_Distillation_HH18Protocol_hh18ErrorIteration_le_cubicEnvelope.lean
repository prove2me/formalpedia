-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18ErrorIteration_le_cubicEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:29:46.876212+00:00
-- url     : https://prove2.me/submissions/4ec2d992-acf8-4028-bb98-4f01f5fe1d4a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
private theorem hh18ErrorIteration_zero
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    hh18ErrorIteration epsilon hsmall 0 = epsilon := by
  rfl
private theorem hh18ErrorIteration_succ
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18ErrorIteration epsilon hsmall (depth + 1) =
      hh18NextInputErrorRate (hh18ErrorIteration epsilon hsmall depth)
        (hh18IterationNextSmall (hh18IterationState epsilon hsmall depth)) := by
  rfl
end HH18Protocol
end Distillation
end QEC
end
end

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
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    (hh18ErrorIteration epsilon hsmall depth).1 ≤
      hh18CubicErrorEnvelope epsilon depth := by
  induction depth with
  | zero =>
      rw [hh18ErrorIteration_zero]
      rfl
  | succ depth ih =>
      rw [hh18ErrorIteration_succ]
      calc
        (hh18NextInputErrorRate (hh18ErrorIteration epsilon hsmall depth)
            (hh18IterationNextSmall (hh18IterationState epsilon hsmall depth))).1 ≤
            (2 * residualCubicCoefficient) *
              (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
          hh18NextInputErrorRate_le_cubic _ _
        _ ≤ hh18IterationScale ^ 2 *
              (hh18ErrorIteration epsilon hsmall depth).1 ^ 3 :=
          mul_le_mul_of_nonneg_right
            two_mul_residualCubicCoefficient_le_iterationScale_sq
            (pow_nonneg (hh18ErrorIteration epsilon hsmall depth).property.1 3)
        _ ≤ hh18IterationScale ^ 2 * (hh18CubicErrorEnvelope epsilon depth) ^ 3 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀
              (hh18ErrorIteration epsilon hsmall depth).property.1 ih 3)
            (sq_nonneg hh18IterationScale)
        _ = hh18CubicErrorEnvelope epsilon (depth + 1) := by rfl
end QEC.Distillation.HH18Protocol
