-- Prove2me | solution 1 for QEC.Semantics.detectableOnWithScalar_iff_projectorEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:15:20.046268+00:00
-- url     : https://prove2.me/submissions/96f3694c-8cbb-47db-99f6-e801c1eda1c9

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Theorems.Thm_QEC_Semantics_projectorEquation_of_detectableOnWithScalar
import Theorems.Thm_QEC_Semantics_detectableOnWithScalar_of_projectorEquation

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution
    (C : QuantumCode H) (E : Operator H) (c : Complex) :
    DetectableOnWithScalar C E c ↔
      (C.projector.comp E).comp C.projector = c • C.projector := by
  constructor
  · exact projectorEquation_of_detectableOnWithScalar
  · exact detectableOnWithScalar_of_projectorEquation
end QEC.Semantics
