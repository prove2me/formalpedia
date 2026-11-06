-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureZeroPlace_ne_infinity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:34:40.304229+00:00
-- url     : https://prove2.me/submissions/f66dc8e3-ed2d-4354-9118-edca3a790a8a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureZeroPlace_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureInfinityPlace_order_generator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    sourceGaloisWClosureZeroPlace m ≠ sourceGaloisWClosureInfinityPlace m := by
  intro hplaces
  have horder := congrArg
    (fun P : GlobalPlace F256 (SourceGaloisWClosureField m) =>
      P.order (sourceGaloisWClosureGenerator m)) hplaces
  change (sourceGaloisWClosureZeroPlace m).order (sourceGaloisWClosureGenerator m) =
    (sourceGaloisWClosureInfinityPlace m).order
      (sourceGaloisWClosureGenerator m) at horder
  rw [sourceGaloisWClosureZeroPlace_order_generator,
    sourceGaloisWClosureInfinityPlace_order_generator] at horder
  norm_num at horder
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
