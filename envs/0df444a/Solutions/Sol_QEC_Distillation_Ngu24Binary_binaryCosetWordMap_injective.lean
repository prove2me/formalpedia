-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryCosetWordMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:58:43.054961+00:00
-- url     : https://prove2.me/submissions/34872b72-bcb7-4145-888d-a6b10094b574

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetWordMap_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) : Function.Injective (binaryCosetWordMap i) := by
  rintro ⟨u, h⟩ ⟨v, k⟩ heq
  rw [binaryCosetWordMap_apply, binaryCosetWordMap_apply] at heq
  have heq' := physicalWordEmbedding_injective _ heq
  have huv := logicalWordEmbedding_injective _
    ((f256SourceInput i).shortenedCosetLabel_eq_implies_logical_eq _ _ h k heq')
  subst v
  have hhk := (f256SourceInput i).shortenedCosetLabel_injective _ heq'
  exact Prod.ext rfl hhk
end QEC.Distillation.Ngu24Binary
