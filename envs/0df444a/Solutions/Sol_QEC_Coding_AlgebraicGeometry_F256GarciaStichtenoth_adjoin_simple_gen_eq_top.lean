-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.adjoin_simple_gen_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:17:52.901471+00:00
-- url     : https://prove2.me/submissions/a931ee57-82fa-44f6-8a14-ebb5d04ae195

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E] (y : E) :
    F⟮AdjoinSimple.gen F y⟯ = ⊤ := by
  apply IntermediateField.map_injective (F⟮y⟯).val
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map]
  change F⟮y⟯ = (F⟮y⟯).val.fieldRange
  exact (IntermediateField.fieldRange_val _).symm
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
