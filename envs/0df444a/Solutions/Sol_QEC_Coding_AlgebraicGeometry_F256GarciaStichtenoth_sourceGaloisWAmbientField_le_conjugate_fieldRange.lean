-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWAmbientField_le_conjugate_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:34:37.795194+00:00
-- url     : https://prove2.me/submissions/95aba138-720c-4026-947a-356fde389071

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWConjugateRestriction_fieldRange_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureAmbient) :
    SourceGaloisWAmbientField m ≤ f.fieldRange := by
  rw [← sourceGaloisWConjugateRestriction_fieldRange_eq m f]
  intro x hx
  rw [AlgHom.mem_fieldRange] at hx ⊢
  obtain ⟨w, rfl⟩ := hx
  exact ⟨sourceGaloisWFieldToSource m w, rfl⟩
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
