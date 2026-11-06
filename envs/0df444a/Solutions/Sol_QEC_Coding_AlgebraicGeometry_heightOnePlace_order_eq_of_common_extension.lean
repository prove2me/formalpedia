-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOnePlace_order_eq_of_common_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:48:39.087494+00:00
-- url     : https://prove2.me/submissions/2db8b03a-f10d-465c-b944-78f34ff7ffff

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_eq_of_common_positive_scaling
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_algebraMap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {k R R' S S' K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [IsDedekindDomain R] [IsDedekindDomain R']
    [IsDedekindDomain S] [IsDedekindDomain S']
    [Algebra k K] [Algebra k L] [Algebra K L]
    [Algebra R K] [IsFractionRing R K] [Algebra R' K] [IsFractionRing R' K]
    [Algebra S L] [IsFractionRing S L] [Algebra S' L] [IsFractionRing S' L]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra R' S'] [FaithfulSMul R' S'] [Module.Finite R' S']
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [Algebra R' L] [IsScalarTower R' K L] [IsScalarTower R' S' L]
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (P' : IsDedekindDomain.HeightOneSpectrum R')
    (Q : IsDedekindDomain.HeightOneSpectrum S)
    (Q' : IsDedekindDomain.HeightOneSpectrum S')
    [Q.asIdeal.LiesOver P.asIdeal] [Q'.asIdeal.LiesOver P'.asIdeal]
    (hupper : (heightOnePlace (k := k) (K := L) Q).order =
      (heightOnePlace (k := k) (K := L) Q').order) :
    (heightOnePlace (k := k) (K := K) P).order =
      (heightOnePlace (k := k) (K := K) P').order := by
  letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Module.IsTorsionFree R' S' := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : NoZeroSMulDivisors R S := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  letI : NoZeroSMulDivisors R' S' := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  letI : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  letI : P'.asIdeal.IsMaximal := P'.isPrime.isMaximal P'.ne_bot
  have he : 0 < P.asIdeal.ramificationIdx' Q.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q.asIdeal P.ne_bot)
  have hf : 0 < P'.asIdeal.ramificationIdx' Q'.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q'.asIdeal P'.ne_bot)
  apply GlobalPlace.order_eq_of_common_positive_scaling _ _ _ _ he hf
  intro x
  by_cases hx : x = 0
  · simp [hx, GlobalPlace.order]
  · rw [← heightOnePlace_order_algebraMap (k := k) (K := K) (L := L) P Q x hx,
      ← heightOnePlace_order_algebraMap (k := k) (K := K) (L := L) P' Q' x hx, hupper]
end QEC.Coding.AlgebraicGeometry
