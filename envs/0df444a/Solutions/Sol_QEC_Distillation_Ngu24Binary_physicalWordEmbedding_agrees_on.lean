-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.physicalWordEmbedding_agrees_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:51:01.155438+00:00
-- url     : https://prove2.me/submissions/469b1192-4bc0-4d05-a21a-697ad7bc6a09

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {J : Type} [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (S : Finset (J × Fin 512))
    (x y : J → F256) (h : ∀ j, j ∈ S.image Prod.fst → x j = y j) :
    ∀ t, t ∈ S → physicalWordEmbedding J x t = physicalWordEmbedding J y t := by
  intro t ht
  change f256MFESigma (x t.1) t.2 = f256MFESigma (y t.1) t.2
  rw [h t.1 (Finset.mem_image.mpr ⟨t, ht, rfl⟩)]
end QEC.Distillation.Ngu24Binary
