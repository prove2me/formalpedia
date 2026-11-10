-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryTaggedEncodingIsometry_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:14:36.542606+00:00
-- url     : https://prove2.me/submissions/11dfa613-6769-4541-918a-c3ca20b22720

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Theorems.Thm_QEC_Distillation_Ngu24Binary_sourceBinaryTaggedEncodingIsometry_basis
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTaggedCosetLabel_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance 2000] QEC.Distillation.Ngu24Binary.binaryTaggedFinDecidableEq
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryTaggedEncodingIsometry i (registerBasisKet u) =
      taggedCosetNormalization (f256SourceInput i) •
        ∑ h : ThreeCopyTag → (f256SourceInput i).H0,
          registerBasisKet (binaryTaggedCosetLabel i u h) := by
  rw [binaryTaggedEncodingIsometry]
  erw [sourceBinaryTaggedEncodingIsometry_basis]
  simp_rw [binaryTaggedCosetLabel_eq]
end QEC.Distillation.Ngu24Binary
