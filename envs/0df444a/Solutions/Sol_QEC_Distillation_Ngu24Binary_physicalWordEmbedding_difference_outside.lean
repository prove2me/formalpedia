-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.physicalWordEmbedding_difference_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:42:20.657861+00:00
-- url     : https://prove2.me/submissions/98dc53d2-07f0-4392-8187-8537cdc292d2

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Theorems.Thm_QEC_Coding_f256MFESigma_injective


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {J : Type} [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (S : Finset (J × Fin 512))
    (x y : J → F256) (h : ∃ j, j ∉ S.image Prod.fst ∧ x j ≠ y j) :
    ∃ t, t ∉ S ∧ physicalWordEmbedding J x t ≠ physicalWordEmbedding J y t := by
  classical
  obtain ⟨j, hj, hxy⟩ := h
  have hsigma : f256MFESigma (x j) ≠ f256MFESigma (y j) :=
    fun heq => hxy (f256MFESigma_injective heq)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hsigma
  refine ⟨(j, k), ?_, hk⟩
  intro hmem
  exact hj (Finset.mem_image.mpr ⟨(j, k), hmem, rfl⟩)
end QEC.Distillation.Ngu24Binary
