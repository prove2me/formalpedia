-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeStalkScalar_SpecMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:44.824437+00:00
-- url     : https://prove2.me/submissions/b3218022-082c-4248-8f69-9621c5d1d26b

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (R S : CommRingCat) (f : R ⟶ S)
    (x : PrimeSpectrum S) (r : R) :
    schemeStalkScalar R (Spec S) (Spec.map f) x r =
      (StructureSheaf.toStalk S x) (f r) := by
  exact stalkMap_toStalk_apply f x r
end QEC.Coding.AlgebraicGeometry
