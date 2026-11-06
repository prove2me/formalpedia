-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:51:34.079058+00:00
-- url     : https://prove2.me/submissions/06de0299-bfed-44eb-acbf-be9b68994200

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_EmbeddedWSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_fieldRange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_simple_gen_eq_top


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
    F256⟮f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ = sourceClosureWBase m := by
  let g := f.comp (sourceGaloisWFieldToSource m)
  have hgen : F256⟮sourceGaloisWFieldGenerator⟯ =
      (⊤ : IntermediateField F256 SourceGaloisWField) :=
    adjoin_simple_gen_eq_top (F := F256) galoisBaseW
  have h := congrArg (fun K : IntermediateField F256 SourceGaloisWField =>
    K.map (g.restrictScalars F256)) hgen
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map] at h
  change F256⟮f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ =
    (g.fieldRange).restrictScalars F256 at h
  exact h.trans (congrArg (IntermediateField.restrictScalars F256)
    (sourceClosureConjugateW_fieldRange m f))
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
