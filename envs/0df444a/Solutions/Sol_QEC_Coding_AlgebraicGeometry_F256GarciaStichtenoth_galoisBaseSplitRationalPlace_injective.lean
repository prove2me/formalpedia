-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisBaseSplitRationalPlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:01:49.626613+00:00
-- url     : https://prove2.me/submissions/2b5b6487-a6ae-4a73-b3d1-3f9008950791

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution :
    Function.Injective galoisBaseSplitRationalPlace := by
  intro a b hab
  have hplace :
      (baseRationalPlace (galoisBaseSplitPointUnit a)).place =
        (baseRationalPlace (galoisBaseSplitPointUnit b)).place :=
    congrArg RationalPlace.place hab
  have hunit := baseRationalPlace_injective hplace
  apply Subtype.ext
  exact congrArg Units.val hunit
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
