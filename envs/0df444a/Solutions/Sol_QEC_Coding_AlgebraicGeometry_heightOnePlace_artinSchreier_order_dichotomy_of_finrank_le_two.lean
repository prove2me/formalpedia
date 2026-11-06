-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOnePlace_artinSchreier_order_dichotomy_of_finrank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:45.185039+00:00
-- url     : https://prove2.me/submissions/a3dd57a2-c022-48fb-ac61-c3c8461eef84

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_dichotomy


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k K] [Algebra k L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra K L] [Algebra R L] [FiniteDimensional K L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L ≤ 2)
    (ha : (heightOnePlace (k := k) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := K) H).order a) :
    (heightOnePlace (k := k) (K := L) J).order y = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := L) J).order y := by
  letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : NoZeroSMulDivisors R S := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  letI : H.asIdeal.IsMaximal := H.isPrime.isMaximal H.ne_bot
  have he0 : 0 < H.asIdeal.ramificationIdx' J.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver J.asIdeal H.ne_bot)
  have he2 : H.asIdeal.ramificationIdx' J.asIdeal ≤ 2 :=
    (Ideal.ramificationIdx_le_finrank S K L J.asIdeal).trans hdegree
  apply (heightOnePlace (k := k) (K := K) H).artinSchreier_root_order_dichotomy
    (heightOnePlace (k := k) (K := L) J) a y
    (H.asIdeal.ramificationIdx' J.asIdeal) he0 he2 hy
  · by_cases ha0 : a = 0
    · simp [ha0, GlobalPlace.order]
    · exact heightOnePlace_order_algebraMap H J a ha0
  · exact ha
end QEC.Coding.AlgebraicGeometry
