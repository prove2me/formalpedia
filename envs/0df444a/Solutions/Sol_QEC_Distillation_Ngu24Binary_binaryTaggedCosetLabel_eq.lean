-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryTaggedCosetLabel_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:58:45.381073+00:00
-- url     : https://prove2.me/submissions/511c0814-002f-4503-91b3-dd48f8b7fed6

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetWordMap_apply


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
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (h : ThreeCopyTag → (f256SourceInput i).H0) :
    taggedPhysicalWordEmbedding (f256SourceInput i).PivotComplement
      (taggedShortenedCosetLabel (f256SourceInput i)
        (logicalWordEmbedding (ThreeCopyTag × Fin (f256MultiplicationLogicalCount i)) u) h) =
      binaryTaggedCosetLabel i u h := by
  funext x
  change _ = binaryCosetWordMap i (extractBlock u x.1, h x.1) x.2
  rw [binaryCosetWordMap_apply]
  rfl
end QEC.Distillation.Ngu24Binary
