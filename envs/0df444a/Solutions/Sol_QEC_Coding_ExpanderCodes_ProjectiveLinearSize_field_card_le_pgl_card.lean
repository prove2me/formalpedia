-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.ProjectiveLinearSize.field_card_le_pgl_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:22.353294+00:00
-- url     : https://prove2.me/submissions/7c5d404b-78c3-4491-8ad7-b998b05d4afd

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveLinearSize_projectiveUpper_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveLinearSize
open Matrix
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.ProjectiveLinearSize
theorem _root_.solution [Finite K] :
    Nat.card K ≤ Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
    Quotient.finite _
  exact Nat.card_le_card_of_injective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL ∘ projectiveUpper)
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp projectiveUpper_injective)
end QEC.Coding.ExpanderCodes.ProjectiveLinearSize
