-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_integralModel_weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:07:03.486078+00:00
-- url     : https://prove2.me/submissions/788c45f7-579f-4046-8d50-c1a2cd95ed0a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_heightOnePrime_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_multiplicity_map_algEquiv_eq


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    multiplicity Q.asIdeal (differentIdeal B C) =
      2 * (H.asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  let N := integralClosure B L
  letI : IsDedekindDomain N := integralClosure.isDedekindDomain B K L
  letI : Module.IsTorsionFree B N := IsIntegralClosure.isTorsionFree B L
  let σ : N ≃ₐ[B] C := IsIntegralClosure.equiv B N L C
  let J : IsDedekindDomain.HeightOneSpectrum N :=
    IsDedekindDomain.HeightOneSpectrum.comap σ.toRingHom σ.surjective Q
  letI : J.asIdeal.LiesOver H.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change H.asIdeal = Ideal.comap (algebraMap B N) (Ideal.comap σ.toRingHom Q.asIdeal)
    rw [Ideal.comap_comap]
    rw [show σ.toRingHom.comp (algebraMap B N) = algebraMap B C by
      ext b
      exact σ.commutes b]
    exact (show Q.asIdeal.LiesOver H.asIdeal from inferInstance).over
  have hweak := quadraticLiteral_heightOnePrime_weakDifferent A B K L
    H J.asIdeal a y hy hdegree hgen ha
  have hmap : Ideal.map σ.toRingHom J.asIdeal = Q.asIdeal :=
    Q.asIdeal.map_comap_of_surjective σ.toRingHom σ.surjective
  have he : H.asIdeal.ramificationIdx' J.asIdeal =
      H.asIdeal.ramificationIdx' Q.asIdeal :=
    H.asIdeal.ramificationIdx_comap_eq σ Q.asIdeal
  calc
    multiplicity Q.asIdeal (differentIdeal B C) =
        multiplicity J.asIdeal (differentIdeal B N) := by
      rw [← hmap]
      exact differentIdeal_multiplicity_map_algEquiv_eq B N C σ J.asIdeal
    _ = 2 * (H.asIdeal.ramificationIdx' Q.asIdeal - 1) := by rw [hweak, he]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
