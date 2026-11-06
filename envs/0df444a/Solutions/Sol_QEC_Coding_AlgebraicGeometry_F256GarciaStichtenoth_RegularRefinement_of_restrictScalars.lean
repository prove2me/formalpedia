-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.of_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:23:19.018933+00:00
-- url     : https://prove2.me/submissions/8eac93a2-4bbf-4593-909b-aae935c9cf8e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_of_restrictScalars

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)
variable {B : Type*} [_root_.Field B] [Algebra F B] [Algebra B E]
  [IsScalarTower F B E]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace RegularRefinement
theorem _root_.solution
    {J L : IntermediateField B E}
    (h : RegularRefinement Q (J.restrictScalars F) (L.restrictScalars F)) :
    RegularRefinement Q J L := by
  have hlift (N : IntermediateField F E)
      (hc : RegularRefinement Q (J.restrictScalars F) N) :
      ∃ N' : IntermediateField B E, N'.restrictScalars F = N ∧ RegularRefinement Q J N' := by
    induction hc with
    | refl => exact ⟨J, rfl, .refl⟩
    | @tail N M hchain hstep ih =>
        obtain ⟨N', hN', ih⟩ := ih
        have hJM := RegularRefinement.le Q (hchain.tail hstep)
        let M' : IntermediateField B E :=
          M.toSubfield.toIntermediateField (fun x => hJM (J.algebraMap_mem x))
        have hedge : RegularQuadraticEdge Q (N'.restrictScalars F) (M'.restrictScalars F) := by
          change RegularQuadraticEdge Q (N'.restrictScalars F) M
          rwa [hN']
        exact ⟨M', rfl, ih.tail (hedge.of_restrictScalars Q)⟩
  obtain ⟨L', hL', hc⟩ := hlift _ h
  have heq : L' = L := IntermediateField.restrictScalars_injective F hL'
  rwa [heq] at hc
end RegularRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
