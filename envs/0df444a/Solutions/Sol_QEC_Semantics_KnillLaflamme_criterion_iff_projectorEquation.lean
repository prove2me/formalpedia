-- Prove2me | solution 1 for QEC.Semantics.KnillLaflamme.criterion_iff_projectorEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:52:30.465562+00:00
-- url     : https://prove2.me/submissions/cda28e09-acce-41ab-87c4-94a9111ed7b8

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Theorems.Thm_QEC_Semantics_KnillLaflamme_projectorConditionWithScalar_of_matrixConditionWithScalar
import Theorems.Thm_QEC_Semantics_KnillLaflamme_matrixConditionWithScalar_of_projectorConditionWithScalar

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
open QEC.Semantics.KnillLaflamme
namespace QEC.Semantics.KnillLaflamme
theorem _root_.solution
    (C : QuantumCode H) (errors : Set (Operator H)) :
    KnillLaflammeCriterion H C errors ↔
      KnillLaflammeProjectorEquation C errors := by
  constructor
  · rintro ⟨scalar, hscalar⟩
    exact ⟨scalar, projectorConditionWithScalar_of_matrixConditionWithScalar hscalar⟩
  · rintro ⟨scalar, hscalar⟩
    exact ⟨scalar, matrixConditionWithScalar_of_projectorConditionWithScalar hscalar⟩
end QEC.Semantics.KnillLaflamme
