-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureZeroPlace_order_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:42:12.037965+00:00
-- url     : https://prove2.me/submissions/9df4f181-cab4-4207-9a7c-ecb4cb5b04a5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivClosureField_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPlace_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order


section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem sourceGaloisWFieldEquivClosureFieldOverF256_generator (m : ℕ) :
    sourceGaloisWFieldEquivClosureFieldOverF256 m sourceGaloisWFieldGenerator =
      sourceGaloisWClosureGenerator m := by
  apply Subtype.ext
  exact sourceGaloisWFieldEquivClosureField_generator m
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    (sourceGaloisWClosureZeroPlace m).order (sourceGaloisWClosureGenerator m) = 1 := by
  rw [sourceGaloisWClosureZeroPlace, GlobalPlace.comapAlgEquiv_order,
    ← sourceGaloisWFieldEquivClosureFieldOverF256_generator,
    (sourceGaloisWFieldEquivClosureFieldOverF256 m).symm_apply_apply]
  exact sourceGaloisWZeroPlace_order_generator
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
