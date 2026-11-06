-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.self_weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:59:56.025108+00:00
-- url     : https://prove2.me/submissions/18d251b0-953c-4782-a91d-1895fc899cf7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_ExponentTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ramificationIdx_and_weakDifferent_of_finrank_eq_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (R : Type*) [CommRing R] [IsDedekindDomain R]
    (H : IsDedekindDomain.HeightOneSpectrum R) :
    multiplicity H.asIdeal (differentIdeal R R) =
      2 * (H.asIdeal.ramificationIdx' H.asIdeal - 1) := by
  letI : H.asIdeal.LiesOver H.asIdeal := ⟨by simp [Ideal.under]⟩
  exact (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    R R (FractionRing R) (FractionRing R) H H (Module.finrank_self _)).2
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
