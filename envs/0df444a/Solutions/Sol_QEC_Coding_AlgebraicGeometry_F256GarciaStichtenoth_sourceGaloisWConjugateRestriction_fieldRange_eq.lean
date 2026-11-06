-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWConjugateRestriction_fieldRange_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:45:03.70997+00:00
-- url     : https://prove2.me/submissions/055d1700-9cb2-4940-888c-f9c4f3159bc4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureAmbient) :
    (f.comp (sourceGaloisWFieldToSource m)).fieldRange =
      SourceGaloisWAmbientField m := by
  let g : SourceGaloisWField →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient :=
    f.comp (sourceGaloisWFieldToSource m)
  let e := sourceGaloisWFieldEquivAmbientField m
  let g' : SourceGaloisWAmbientField m →ₐ[GaloisBaseField]
      SourceGaloisClosureAmbient := g.comp e.symm.toAlgHom
  have hnormal : g'.fieldRange = SourceGaloisWAmbientField m :=
    AlgHom.fieldRange_of_normal g'
  have heTop : e.symm.toAlgHom.fieldRange = ⊤ :=
    AlgHom.fieldRange_eq_top.mpr e.symm.surjective
  have hrange : g'.fieldRange = g.fieldRange := by
    calc
      g'.fieldRange = e.symm.toAlgHom.fieldRange.map g :=
        (AlgHom.map_fieldRange e.symm.toAlgHom g).symm
      _ = (⊤ : IntermediateField GaloisBaseField
          SourceGaloisWField).map g := by rw [heTop]
      _ = g.fieldRange := (AlgHom.fieldRange_eq_map g).symm
  exact hrange.symm.trans hnormal
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
