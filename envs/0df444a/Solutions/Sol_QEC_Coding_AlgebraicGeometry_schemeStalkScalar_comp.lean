-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeStalkScalar_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:41.122636+00:00
-- url     : https://prove2.me/submissions/e4ffd283-d684-4bfe-aecc-9a2ab6ab5e3c

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (R : CommRingCat) (X Y : Scheme)
    (g : X ⟶ Y) (f : Y ⟶ Spec R) (x : X) (r : R) :
    (g.stalkMap x) (schemeStalkScalar R Y f (g x) r) =
      schemeStalkScalar R X (g ≫ f) x r := by
  unfold schemeStalkScalar
  rw [Scheme.Hom.stalkMap_comp]
  rfl
end QEC.Coding.AlgebraicGeometry
