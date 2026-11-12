-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.stage_success_one_sub_fifteen_rate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:27:14.737162+00:00
-- url     : https://prove2.me/submissions/966dbe03-5c78-4a5a-afdd-449ae0cb4807

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_allZeroWord_le
import Theorems.Thm_QEC_Distillation_HH18Protocol_resourceCount_eq_fifteen


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
    1 - 15 * (hh18ErrorIteration epsilon hsmall depth).1 ≤
      rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by
  have hrate : 0 ≤ (hh18ErrorIteration epsilon hsmall depth).1 :=
    (hh18ErrorIteration epsilon hsmall depth).property.1
  calc
    1 - 15 * (hh18ErrorIteration epsilon hsmall depth).1 ≤
        (1 - (hh18ErrorIteration epsilon hsmall depth).1) ^ 15 := by
      have hbernoulli := one_add_mul_sub_le_pow
        (a := 1 - (hh18ErrorIteration epsilon hsmall depth).1)
        (by linarith [(hh18ErrorIteration epsilon hsmall depth).property.2]) 15
      calc
        1 - 15 * (hh18ErrorIteration epsilon hsmall depth).1 =
            1 + 15 * ((1 - (hh18ErrorIteration epsilon hsmall depth).1) - 1) := by ring
        _ ≤ (1 - (hh18ErrorIteration epsilon hsmall depth).1) ^ 15 := hbernoulli
    _ = (1 - (hh18ErrorIteration epsilon hsmall depth).1) ^ resourceCount := by
      rw [resourceCount_eq_fifteen]
    _ ≤ rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) :=
      rawSuccessMass_allZeroWord_le _
end QEC.Distillation.HH18Protocol
