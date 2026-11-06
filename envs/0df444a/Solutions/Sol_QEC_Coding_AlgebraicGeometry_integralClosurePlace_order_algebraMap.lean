-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.integralClosurePlace_order_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:17:18.555325+00:00
-- url     : https://prove2.me/submissions/e0553439-9416-44c2-87ce-f8cf856bde90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_maximalIdeal_eq_span_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
private theorem integralClosurePlace_order_integral
    {O L : Type*} [CommRing O] [_root_.Field L] [Algebra k L]
    [Algebra O L] [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    {z : integralClosure O L} (hz : z ≠ 0) :
    (integralClosurePlace (k := k) H).order
        (algebraMap (integralClosure O L) L z) =
      (multiplicity H.asIdeal (Ideal.span {z}) : ℤ) := by
  unfold integralClosurePlace GlobalPlace.order
  rw [H.valuation_of_algebraMap,
    H.intValuation_eq_exp_neg_multiplicity hz, WithZero.log_exp]
  ring
private theorem integralClosurePlace_order_integralUnit
    {O L : Type*} [CommRing O] [_root_.Field L] [Algebra k L]
    [Algebra O L] [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    (u : Oˣ) :
    (integralClosurePlace (k := k) H).order
        (algebraMap (integralClosure O L) L
          (algebraMap O (integralClosure O L) (u : O))) = 0 := by
  let C := integralClosure O L
  let uC : Cˣ := Units.map (algebraMap O C) u
  have huC_ne : (uC : C) ≠ 0 := uC.ne_zero
  change (integralClosurePlace (k := k) H).order
    (algebraMap C L (uC : C)) = 0
  rw [integralClosurePlace_order_integral H huC_ne]
  have huC_unit : IsUnit (uC : C) := uC.isUnit
  rw [Ideal.span_singleton_eq_top.mpr huC_unit]
  norm_cast
  have hH_nonunit : ¬ IsUnit H.asIdeal := by
    rw [Ideal.isUnit_iff]
    exact H.isPrime.ne_top
  simpa only [Ideal.one_eq_top] using multiplicity_of_one_right hH_nonunit
private theorem integralClosurePlace_order_uniformizer
    {K L : Type*} [_root_.Field K] [_root_.Field L] [Algebra k K]
    [Algebra k L] [Algebra K L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    (H : IsDedekindDomain.HeightOneSpectrum
      (integralClosure P.valuationRing L)) :
    (integralClosurePlace (k := k) H).order
        (algebraMap K L
          (algebraMap P.valuationRing K P.uniformizerInValuationRing)) =
      ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal : ℤ) := by
  let O := P.valuationRing
  let C := integralClosure O L
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let t : O := P.uniformizerInValuationRing
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O L := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    intro x y hxy
    apply ValuationSubring.subtype_injective O
    apply (algebraMap K L).injective
    simp only [IsScalarTower.algebraMap_apply O K L,
      ValuationSubring.algebraMap_apply] at hxy
    exact hxy
  letI : Module.IsTorsionFree O C := IsIntegralClosure.isTorsionFree O L
  letI : FaithfulSMul O C :=
    Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : IsScalarTower O C L := IsScalarTower.of_algebraMap_eq' rfl
  have hm_ne_bot : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap_ne_bot : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm_ne_bot
  have hm_span : m = Ideal.span ({t} : Set O) := by
    simpa only [O, m, t] using P.maximalIdeal_eq_span_uniformizer
  have ht_irreducible : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr hm_span
  have ht_ne : algebraMap O C t ≠ 0 := by
    simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective O C).ne ht_irreducible.ne_zero
  have hspan : Ideal.span ({algebraMap O C t} : Set C) =
      Ideal.map (algebraMap O C) m := by
    calc
      Ideal.span ({algebraMap O C t} : Set C) =
          Ideal.map (algebraMap O C) (Ideal.span ({t} : Set O)) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap O C) m := by rw [← hm_span]
  rw [← IsScalarTower.algebraMap_apply O K L,
    IsScalarTower.algebraMap_apply O C L]
  rw [integralClosurePlace_order_integral H ht_ne]
  norm_cast
  calc
    multiplicity H.asIdeal (Ideal.span ({algebraMap O C t} : Set C)) =
        multiplicity H.asIdeal (Ideal.map (algebraMap O C) m) := by rw [hspan]
    _ = m.ramificationIdx' H.asIdeal :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
        hmap_ne_bot H.isPrime).symm
private theorem integralClosureOrder_zpow
    {k L : Type*} [_root_.Field k] [Finite k] [_root_.Field L] [Algebra k L]
    (P : GlobalPlace k L) (z : L) (n : ℤ) :
    P.order (z ^ n) = n * P.order z := by
  unfold GlobalPlace.order
  rw [map_zpow₀, WithZero.log_zpow]
  simp only [smul_eq_mul]
  ring
private theorem integralClosureOrder_baseUnit
    {K : Type*} [_root_.Field K] [Algebra k K]
    (P : GlobalPlace k K) (u : P.valuationRingˣ) :
    P.order (algebraMap P.valuationRing K (u : P.valuationRing)) = 0 := by
  let u' : P.valuationRing.unitGroup :=
    P.valuationRing.unitGroupMulEquiv.symm u
  have hu' : P.valuation ((u' : Kˣ) : K) = 1 :=
    (Valuation.mem_unitGroup_iff K P.valuation (u' : Kˣ)).mp u'.property
  have hu : P.valuation
      (algebraMap P.valuationRing K (u : P.valuationRing)) = 1 := by
    simp only [u', ValuationSubring.coe_unitGroupMulEquiv_symm_apply] at hu'
    exact hu'
  unfold GlobalPlace.order
  rw [hu, WithZero.log_one]
  simp
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {K L : Type*} [_root_.Field K] [_root_.Field L] [Algebra k K]
    [Algebra k L] [Algebra K L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [hDedekind : IsDedekindDomain
      (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    (H : IsDedekindDomain.HeightOneSpectrum
      (integralClosure P.valuationRing L))
    (y : K) (hy : y ≠ 0) :
    (integralClosurePlace (k := k) H).order
        (algebraMap K L y) =
      ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal : ℤ) *
        P.order y := by
  let O := P.valuationRing
  let C := integralClosure O L
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q := integralClosurePlace (k := k) H
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  have ht_irreducible : Irreducible P.uniformizerInValuationRing := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer
      P.uniformizerInValuationRing).mpr
    exact P.maximalIdeal_eq_span_uniformizer
  obtain ⟨n, u, hyfactor⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      ht_irreducible hy
  have hyfactor' :
      y = algebraMap O K (u : O) *
        algebraMap O K P.uniformizerInValuationRing ^ n := by
    simpa only [O, Units.smul_def, Algebra.smul_def] using hyfactor
  have ht_lower :
      P.order (algebraMap O K P.uniformizerInValuationRing) = 1 := by
    change P.order P.uniformizer = 1
    exact P.order_uniformizer
  have hu_lower : P.order (algebraMap O K (u : O)) = 0 := by
    simpa only [O] using
      integralClosureOrder_baseUnit P u
  have htK_ne : algebraMap O K P.uniformizerInValuationRing ≠ 0 := by
    intro ht0
    apply ht_irreducible.ne_zero
    apply Subtype.ext
    exact ht0
  have huK_ne : algebraMap O K (u : O) ≠ 0 := by
    intro hu0
    apply u.ne_zero
    apply Subtype.ext
    exact hu0
  have hn_lower : P.order y = n := by
    rw [hyfactor', P.order_mul huK_ne (zpow_ne_zero n htK_ne),
      integralClosureOrder_zpow, hu_lower, ht_lower]
    ring
  have hyfactorUpper := congrArg (algebraMap K L) hyfactor'
  simp only [map_mul, map_zpow₀] at hyfactorUpper
  have hu_upper : Q.order
      (algebraMap K L (algebraMap O K (u : O))) = 0 := by
    letI : IsScalarTower O C L := IsScalarTower.of_algebraMap_eq' rfl
    rw [← IsScalarTower.algebraMap_apply O K L,
      IsScalarTower.algebraMap_apply O C L]
    exact integralClosurePlace_order_integralUnit H u
  have ht_upper : Q.order
      (algebraMap K L (algebraMap O K P.uniformizerInValuationRing)) =
        (m.ramificationIdx' H.asIdeal : ℤ) := by
    simpa only [O, m, Q] using
      integralClosurePlace_order_uniformizer P H
  calc
    Q.order (algebraMap K L y) =
        Q.order (algebraMap K L (algebraMap O K (u : O)) *
          algebraMap K L (algebraMap O K P.uniformizerInValuationRing) ^ n) := by
      rw [hyfactorUpper]
    _ = Q.order (algebraMap K L (algebraMap O K (u : O))) +
        Q.order (algebraMap K L
          (algebraMap O K P.uniformizerInValuationRing) ^ n) := by
      apply GlobalPlace.order_mul
      · simpa only [map_zero] using (algebraMap K L).injective.ne huK_ne
      · exact zpow_ne_zero n (by
          simpa only [map_zero] using (algebraMap K L).injective.ne htK_ne)
    _ = 0 + n * (m.ramificationIdx' H.asIdeal : ℤ) := by
      rw [integralClosureOrder_zpow, hu_upper, ht_upper]
    _ = (m.ramificationIdx' H.asIdeal : ℤ) * P.order y := by
      rw [hn_lower]
      ring
end QEC.Coding.AlgebraicGeometry
