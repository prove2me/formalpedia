-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularQuadraticEdge.of_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:17:33.011211+00:00
-- url     : https://prove2.me/submissions/7ac1dee8-a5b7-4bb1-83ce-f0d547ef967b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)
variable {B : Type*} [_root_.Field B] [Algebra F B] [Algebra B E]
  [IsScalarTower F B E]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace RegularQuadraticEdge
theorem _root_.solution
    {J L : IntermediateField B E}
    (h : RegularQuadraticEdge Q (J.restrictScalars F) (L.restrictScalars F)) :
    RegularQuadraticEdge Q J L := by
  obtain ⟨y, hy, ha, hgen⟩ := h
  refine ⟨y, hy, ha, ?_⟩
  have hsmall : ((J.restrictScalars F)⟮y⟯).restrictScalars F = L.restrictScalars F := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, ← hgen]
  apply IntermediateField.restrictScalars_injective F
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup B J ({y} : Set E)]
  exact hsmall.symm
end RegularQuadraticEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
