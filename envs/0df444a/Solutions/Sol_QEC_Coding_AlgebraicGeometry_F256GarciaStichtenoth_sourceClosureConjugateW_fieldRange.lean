-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:48:08.401656+00:00
-- url     : https://prove2.me/submissions/ddac308e-93c4-43eb-84bc-efc860fa909a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWConjugateRestriction_fieldRange_eq


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceConstantBaseTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wConstantBaseTower
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m) :
    (f.comp (sourceGaloisWFieldToSource m)).fieldRange = SourceGaloisWClosureField m := by
  let v := (IntermediateField.normalClosure GaloisBaseField (SourceField m)
    SourceGaloisClosureAmbient).val
  apply IntermediateField.map_injective v
  change (f.comp (sourceGaloisWFieldToSource m)).fieldRange.map v =
    (sourceGaloisWFieldToClosure m).fieldRange.map v
  rw [AlgHom.map_fieldRange, AlgHom.map_fieldRange]
  exact (sourceGaloisWConjugateRestriction_fieldRange_eq m (v.comp f)).trans
    (sourceGaloisWConjugateRestriction_fieldRange_eq m (v.comp (sourceGaloisSeedToClosure m))).symm
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
