-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.integralClosurePlace_artinSchreier_order_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:21.674416+00:00
-- url     : https://prove2.me/submissions/7bc7ec92-9af4-43b0-9294-4fa3a9b8998b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_integralClosurePlace_order_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_dichotomy
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [Algebra.IsSeparable K L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    (H : IsDedekindDomain.HeightOneSpectrum
      (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (hdegree : Module.finrank K L = 2)
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    (integralClosurePlace (k := k) H).order y = -1 ∨
      0 ≤ (integralClosurePlace (k := k) H).order y := by
  let O := P.valuationRing
  let C := integralClosure O L
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  letI : Module.IsTorsionFree O L :=
    Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : Module.IsTorsionFree O C := IsIntegralClosure.isTorsionFree O L
  letI : Module.Finite O C := IsIntegralClosure.finite O K L C
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have he0 : 0 < m.ramificationIdx' H.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver H.asIdeal hm0)
  have he2 : m.ramificationIdx' H.asIdeal ≤ 2 := by
    rw [← hdegree]
    exact Ideal.ramificationIdx_le_finrank C K L H.asIdeal
  apply P.artinSchreier_root_order_dichotomy
    (integralClosurePlace (k := k) H) a y (m.ramificationIdx' H.asIdeal) he0 he2 hy
  · by_cases ha0 : a = 0
    · simp [ha0, GlobalPlace.order]
    · exact integralClosurePlace_order_algebraMap P H a ha0
  · exact ha
end QEC.Coding.AlgebraicGeometry
