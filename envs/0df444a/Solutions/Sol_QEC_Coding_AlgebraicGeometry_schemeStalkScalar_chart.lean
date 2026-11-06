-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeStalkScalar_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:22.985128+00:00
-- url     : https://prove2.me/submissions/0c7d6e56-2107-4b45-9607-f4408256a8ff

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeStalkScalar_comp
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeStalkScalar_SpecMap

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (R S : CommRingCat) (Y : Scheme)
    (g : Spec S ⟶ Y) (f : Y ⟶ Spec R) (u : R ⟶ S)
    (h : g ≫ f = Spec.map u) (x : PrimeSpectrum S) (r : R) :
    (g.stalkMap x) (schemeStalkScalar R Y f (g x) r) =
      StructureSheaf.toStalk S x (u r) := by
  exact (schemeStalkScalar_comp R (Spec S) Y g f x r).trans
    ((congrArg (fun m => schemeStalkScalar R (Spec S) m x r) h).trans
      (schemeStalkScalar_SpecMap R S u x r))
end QEC.Coding.AlgebraicGeometry
