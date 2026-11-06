-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.weakDifferent_tower_of_fractionFields
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:00:47.568448+00:00
-- url     : https://prove2.me/submissions/aaa6c043-d981-4b9c-8b0b-b1718e373677

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_ExponentTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_differentIdeal_multiplicity_eq_two_mul_ramificationIdx_sub_one_tower


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite B C] [Module.Finite A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
    [Algebra A K] [IsFractionRing A K] [Algebra C L] [IsFractionRing C L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C L]
    [Algebra.IsSeparable K L]
    (p : IsDedekindDomain.HeightOneSpectrum A)
    (P : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C)
    [P.asIdeal.LiesOver p.asIdeal] [Q.asIdeal.LiesOver P.asIdeal]
    (hAB : multiplicity P.asIdeal (differentIdeal A B) =
      2 * (p.asIdeal.ramificationIdx' P.asIdeal - 1))
    (hBC : multiplicity Q.asIdeal (differentIdeal B C) =
      2 * (P.asIdeal.ramificationIdx' Q.asIdeal - 1)) :
    multiplicity Q.asIdeal (differentIdeal A C) =
      2 * (p.asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  letI : Algebra.IsSeparable (FractionRing A) (FractionRing C) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv A K).symm.toRingEquiv
      (FractionRing.algEquiv C L).symm.toRingEquiv ?_
    apply IsFractionRing.ringHom_ext (A := A)
    intro x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv A K).symm (FractionRing.algEquiv C L).symm
      (algebraMap A K x)
  exact differentIdeal_multiplicity_eq_two_mul_ramificationIdx_sub_one_tower
    A B C p.asIdeal P.asIdeal Q.asIdeal p.ne_bot hAB hBC
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
