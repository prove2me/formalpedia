-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursion_adjoin_coordinate_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:34:44.428217+00:00
-- url     : https://prove2.me/submissions/114fbc23-9e5f-447e-8313-4aef99f26163

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    (SourceField m)⟮sourceDistinguishedCoordinate (m + 1)⟯ =
      (⊤ : IntermediateField (SourceField m) (SourceField (m + 1))) := by
  let P := sourceDistinguishedPlace m
  let x := sourceDistinguishedCoordinate m
  let hx := sourceDistinguishedCoordinate_order m
  apply top_unique
  have hroot : (SourceField m)⟮(AdjoinRoot.root (sourceStepPolynomial P x hx) :
      SourceField (m + 1))⟯ = ⊤ :=
    IntermediateField.adjoin_root_eq_top (sourceStepPolynomial P x hx)
  refine hroot.symm.le.trans ?_
  erw [IntermediateField.adjoin_le_iff]
  intro z hz
  have hz' : z = AdjoinRoot.root (sourceStepPolynomial P x hx) := Set.mem_singleton_iff.mp hz
  subst z
  have hmem := ((SourceField m)⟮sourceDistinguishedCoordinate (m + 1)⟯).inv_mem
    (mem_adjoin_simple_self (SourceField m) (sourceDistinguishedCoordinate (m + 1)))
  have hcoord : (sourceDistinguishedCoordinate (m + 1))⁻¹ =
      (AdjoinRoot.root (sourceStepPolynomial P x hx) : SourceField (m + 1)) :=
    inv_inv _
  rw [hcoord] at hmem
  exact hmem
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
