-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureInfinityPlace_order_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:41:33.027619+00:00
-- url     : https://prove2.me/submissions/5012ce36-d49d-477b-880a-1a81174c3999

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivClosureField_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPlace_order_generator
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
    (sourceGaloisWClosureInfinityPlace m).order (sourceGaloisWClosureGenerator m) = -1 := by
  rw [sourceGaloisWClosureInfinityPlace, GlobalPlace.comapAlgEquiv_order,
    ← sourceGaloisWFieldEquivClosureFieldOverF256_generator,
    (sourceGaloisWFieldEquivClosureFieldOverF256 m).symm_apply_apply]
  exact sourceGaloisWInfinityPlace_order_generator
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
