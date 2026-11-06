-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureField_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:34:08.733566+00:00
-- url     : https://prove2.me/submissions/dc713c11-2a3f-4a28-8620-7067eab5685b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWField_finrank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    Module.finrank GaloisBaseField (SourceGaloisWClosureField m) = 15 := by
  let e : SourceGaloisWField ≃ₐ[GaloisBaseField] SourceGaloisWClosureField m :=
    AlgEquiv.ofInjectiveField (sourceGaloisWFieldToClosure m)
  calc
    Module.finrank GaloisBaseField (SourceGaloisWClosureField m) =
        Module.finrank GaloisBaseField SourceGaloisWField :=
      e.toLinearEquiv.finrank_eq.symm
    _ = 15 := sourceGaloisWField_finrank
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
