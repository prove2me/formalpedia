-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.sourceBinaryTaggedEncodingIsometry_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:02:54.728204+00:00
-- url     : https://prove2.me/submissions/7957eef9-0590-4b37-9e5a-457b268e711d

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedLogicalIsometry_basis
import Theorems.Thm_QEC_Distillation_Ngu24Binary_taggedPhysicalIsometry_basis

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance 2000] QEC.Distillation.Ngu24Binary.binaryTaggedFinDecidableEq
variable {I Logical : Type} [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryTaggedLogicalDecidableEq
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (data : SourceInput F256 I Logical)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) Logical) :
    sourceBinaryTaggedEncodingIsometry data (registerBasisKet u) =
      taggedCosetNormalization data • ∑ h : ThreeCopyTag → data.H0,
        registerBasisKet (taggedPhysicalWordEmbedding data.PivotComplement
          (taggedShortenedCosetLabel data (logicalWordEmbedding (ThreeCopyTag × Logical) u) h)) := by
  change taggedPhysicalIsometry _ (taggedEncodingLinearMap data
    (taggedLogicalIsometry Logical (registerBasisKet u))) = _
  rw [taggedLogicalIsometry_basis, taggedEncodingLinearMap_apply_logical_basis]
  unfold taggedShortenedCosetKet
  rw [map_smul, map_sum]
  simp_rw [taggedPhysicalIsometry_basis]
end QEC.Distillation.Ngu24Binary
