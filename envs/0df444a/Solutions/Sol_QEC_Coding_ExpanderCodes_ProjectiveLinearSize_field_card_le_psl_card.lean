-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.ProjectiveLinearSize.field_card_le_psl_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:30:58.65693+00:00
-- url     : https://prove2.me/submissions/608f3903-b5a4-4123-b02e-c51d9ec6a7f5

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
    Nat.card K ≤ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
  Nat.card_le_card_of_injective projectiveUpper projectiveUpper_injective
end QEC.Coding.ExpanderCodes.ProjectiveLinearSize
