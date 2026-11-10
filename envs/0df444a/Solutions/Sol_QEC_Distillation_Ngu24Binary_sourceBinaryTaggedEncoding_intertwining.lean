-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.sourceBinaryTaggedEncoding_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:21:23.35423+00:00
-- url     : https://prove2.me/submissions/9efd09aa-5e7c-4e3b-b43b-289ef410e7a8

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPhysicalCCZ_intertwines_physicalIsometry
import Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedLogicalIsometry_intertwines_binaryLogicalCCZ
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhysicalTransport_implements_logical


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
variable {I Logical : Type} [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCubicLogicalDecidableEq
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (data : SourceInput F256 I Logical)
    (psi : TaggedThreeCopyRegister (ZMod 2) Logical) :
    binaryPhysicalCCZ (sourceBinaryTaggedEncodingIsometry data psi) =
      sourceBinaryTaggedEncodingIsometry data (binaryLogicalCCZ psi) := by
  change binaryPhysicalCCZ (taggedPhysicalIsometry _
    (taggedEncodingLinearMap data (taggedLogicalIsometry Logical psi))) =
    taggedPhysicalIsometry _ (taggedEncodingLinearMap data
      (taggedLogicalIsometry Logical (binaryLogicalCCZ psi)))
  have hp := LinearMap.congr_fun
    (binaryPhysicalCCZ_intertwines_physicalIsometry (J := data.PivotComplement))
      (taggedEncodingLinearMap data (taggedLogicalIsometry Logical psi))
  change binaryPhysicalCCZ (taggedPhysicalIsometry _ _) = taggedPhysicalIsometry _ _ at hp
  rw [hp]
  have hq := taggedCubicPhysicalTransport_implements_logical data f256RMFEpsi
    (taggedLogicalIsometry Logical psi)
  change taggedCubicPhysicalTransport f256RMFEpsi (taggedEncodingLinearMap data _) =
    taggedEncodingLinearMap data (taggedCubicPhaseTransport f256RMFEpsi Finset.univ _) at hq
  erw [hq]
  have hl := LinearMap.congr_fun
    (taggedLogicalIsometry_intertwines_binaryLogicalCCZ (J := Logical)) psi
  exact congrArg (fun x => taggedPhysicalIsometry data.PivotComplement
    (taggedEncodingLinearMap data x)) hl
end QEC.Distillation.Ngu24Binary
