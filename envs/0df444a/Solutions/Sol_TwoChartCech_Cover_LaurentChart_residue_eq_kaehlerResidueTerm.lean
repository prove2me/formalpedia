-- Prove2me | solution 1 for TwoChartCech.Cover.LaurentChart.residue_eq_kaehlerResidueTerm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/17ba9853-231d-5e84-8715-4f3c7a1ebc39

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicCurve_LocalResidue
import Theorems.Thm_RingHom_laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul
import Theorems.Thm_AlgebraicCurve_Place_algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_Cover_LaurentChart_residue_eq_kaehlerResidueTerm
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"

universe u v w

open AlgebraicCurve in
theorem solution {k : Type u} [Field k] {F : Type v} [Field F] [Algebra k F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar k F]
    {𝒰 : TwoChartCech.Cover.{u, w} k} (Λ : 𝒰.LaurentChart) (ψ : 𝒰.A01 →ₐ[k] F)
    (Φ : Ω[𝒰.A01⁄k] →ₗ[k] Ω[F⁄k])
    (hΦ : ∀ s g : 𝒰.A01, Φ (s • KaehlerDifferential.D k 𝒰.A01 g) = ψ s • KaehlerDifferential.D k F (ψ g))
    (Λ' : F →+* LaurentSeries k) (hΛ' : ∀ y : 𝒰.A01, Λ' (ψ y) = Λ.expand y)
    (v : AlgebraicCurve.Place k F) [v.DCoordGenerates] [Nontrivial Ω[F⁄k]]
    (hΛv : ∀ f : F, f ∈ v.toValuationSubring ↔ Λ' f ∈ (HahnSeries.ofPowerSeries ℤ k).range)
    {t₀ : F} (ht₀ : Λ' t₀ = HahnSeries.single 1 1) (η : Ω[𝒰.A01⁄k]) :
    Λ.residue η = AlgebraicCurve.kaehlerResidueTerm (Φ η) (AlgebraicCurve.diagonalHom k F 1) v := by
  classical

  have hΛC : ∀ c : k, Λ' (algebraMap k F c) = HahnSeries.C c := fun c => by
    rw [show algebraMap k F c = ψ (algebraMap k 𝒰.A01 c) from (ψ.commutes c).symm, hΛ', Λ.expand_algebraMap]

  obtain ⟨hder, hDt₀'⟩ :=
    RingHom.laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul (R := k) (A := F) Λ' hΛC ht₀
  have hDt₀ : KaehlerDifferential.D k F t₀ ≠ 0 := hDt₀' inferInstance

  have hdc_ne : v.differentialCoeff (KaehlerDifferential.D k F t₀) ≠ 0 := fun h0 =>
    hDt₀ (by rw [← v.differentialCoeff_smul_dCoord (KaehlerDifferential.D k F t₀), h0, zero_smul])
  let coef : Ω[F⁄k] → F := fun ω => v.differentialCoeff ω / v.differentialCoeff (KaehlerDifferential.D k F t₀)
  have hcoef : ∀ ω : Ω[F⁄k], ω = coef ω • KaehlerDifferential.D k F t₀ := fun ω => by
    conv_rhs => rw [← v.differentialCoeff_smul_dCoord (KaehlerDifferential.D k F t₀)]
    rw [smul_smul, div_mul_cancel₀ _ hdc_ne, v.differentialCoeff_smul_dCoord]
  have hdc_eq : ∀ ω : Ω[F⁄k],
      v.differentialCoeff ω = coef ω * v.differentialCoeff (KaehlerDifferential.D k F t₀) := fun ω => by
    conv_lhs => rw [hcoef ω]
    rw [v.differentialCoeff_smul]
  have hdc_add : ∀ ω ω' : Ω[F⁄k],
      v.differentialCoeff (ω + ω') = v.differentialCoeff ω + v.differentialCoeff ω' := fun ω ω' =>
    v.differentialCoeff_unique
      (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])
  have hcD : ∀ g : F, LaurentSeries.derivative k (Λ' g) = Λ' (coef (KaehlerDifferential.D k F g)) :=
    fun g => hder g _ (hcoef _)

  have hps : ∀ f : F, f ∈ v.toValuationSubring → ∃ p : PowerSeries k, Λ' f = HahnSeries.ofPowerSeries ℤ k p :=
    fun f hf => by obtain ⟨p, hp⟩ := (hΛv f).mp hf; exact ⟨p, hp.symm⟩
  have hmem_of : ∀ (f : F) (p : PowerSeries k), Λ' f = HahnSeries.ofPowerSeries ℤ k p →
      f ∈ v.toValuationSubring := fun f p hp => (hΛv f).mpr ⟨p, hp.symm⟩
  have hinvps : ∀ p : PowerSeries k, PowerSeries.constantCoeff p ≠ 0 →
      ∃ q : PowerSeries k, (HahnSeries.ofPowerSeries ℤ k p)⁻¹ = HahnSeries.ofPowerSeries ℤ k q := by
    intro p hc
    obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hc)
    refine ⟨↑u⁻¹, inv_eq_of_mul_eq_one_right ?_⟩
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  have hcc_ne_of_unit : ∀ (y : v.toValuationSubring) (p : PowerSeries k),
      Λ' y = HahnSeries.ofPowerSeries ℤ k p → IsUnit y → PowerSeries.constantCoeff p ≠ 0 := by
    intro y p hp hy
    obtain ⟨z, hz⟩ := hy.exists_right_inv
    obtain ⟨q, hq⟩ := hps z z.2
    have hz' : (y : F) * z = 1 := by
      have := congrArg Subtype.val hz
      simpa using this
    have h1' : HahnSeries.ofPowerSeries ℤ k (p * q) = HahnSeries.ofPowerSeries ℤ k 1 := by
      rw [map_mul, ← hp, ← hq, ← map_mul, hz', map_one, map_one]
    have h1 : p * q = 1 := HahnSeries.ofPowerSeries_injective h1'
    have h2 := congrArg PowerSeries.constantCoeff h1
    rw [map_mul, map_one] at h2
    exact left_ne_zero_of_mul_eq_one h2

  have hsurj : Function.Surjective (algebraMap k v.ResidueField) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp⟩ := hps y y.2
    refine ⟨PowerSeries.constantCoeff p, ?_⟩
    rw [IsScalarTower.algebraMap_apply k v.toValuationSubring v.ResidueField, eq_comm, ← sub_eq_zero]
    change IsLocalRing.residue _ y - IsLocalRing.residue _ (algebraMap k _ (PowerSeries.constantCoeff p)) = 0
    rw [← map_sub]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine hcc_ne_of_unit _ (p - PowerSeries.C (PowerSeries.constantCoeff p)) ?_ hu (by simp)
    change Λ' ((y : F) - (algebraMap k v.toValuationSubring (PowerSeries.constantCoeff p) : F)) = _
    rw [Place.coe_algebraMap, map_sub, hp, hΛC, map_sub, HahnSeries.ofPowerSeries_C]
  have htr : ∀ x : k, Algebra.trace k v.ResidueField (algebraMap k _ x) = x := by
    intro x
    have e : k ≃ₐ[k] v.ResidueField :=
      AlgEquiv.ofBijective (Algebra.ofId k _) ⟨(algebraMap k v.ResidueField).injective, hsurj⟩
    rw [Algebra.trace_algebraMap, ← e.toLinearEquiv.finrank_eq, Module.finrank_self, one_smul]

  set ϖ : v.toValuationSubring := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose
    with hϖdef
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  have hdC : v.dCoord = KaehlerDifferential.D k F (ϖ : F) := rfl
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖirr.ne_zero (Subtype.ext h)
  have hmax : IsLocalRing.maximalIdeal v.toValuationSubring = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have ht₀mem : t₀ ∈ v.toValuationSubring :=
    hmem_of t₀ PowerSeries.X (by rw [ht₀, HahnSeries.ofPowerSeries_X])
  have ht₀nu : ¬ IsUnit (⟨t₀, ht₀mem⟩ : v.toValuationSubring) := fun hu =>
    hcc_ne_of_unit ⟨t₀, ht₀mem⟩ PowerSeries.X (by rw [HahnSeries.ofPowerSeries_X]; exact ht₀) hu
      PowerSeries.constantCoeff_X
  have ht₀max : (⟨t₀, ht₀mem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := ht₀nu
  rw [hmax, Ideal.mem_span_singleton'] at ht₀max
  obtain ⟨w, hw⟩ := ht₀max
  obtain ⟨pϖ, hpϖ⟩ := hps ϖ ϖ.2
  obtain ⟨pw, hpw⟩ := hps w w.2
  have hcc_ϖ : PowerSeries.constantCoeff pϖ = 0 := by
    by_contra hne
    apply hϖirr.not_isUnit
    obtain ⟨q, hq⟩ := hinvps pϖ hne
    have hinv : (ϖ : F)⁻¹ ∈ v.toValuationSubring := hmem_of _ q (by rw [map_inv₀, hpϖ, hq])
    exact isUnit_iff_exists_inv.mpr ⟨⟨(ϖ : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hϖ0)⟩
  obtain ⟨r, hr⟩ := PowerSeries.X_dvd_iff.mpr hcc_ϖ
  have hX' : HahnSeries.ofPowerSeries ℤ k PowerSeries.X = HahnSeries.ofPowerSeries ℤ k (pw * pϖ) := by
    rw [HahnSeries.ofPowerSeries_X, map_mul, ← hpw, ← hpϖ, ← map_mul, ← ht₀]
    exact congrArg (fun z : v.toValuationSubring => Λ' (z : F)) hw.symm
  have hX : PowerSeries.X = pw * pϖ := HahnSeries.ofPowerSeries_injective hX'
  have hccr : PowerSeries.constantCoeff r ≠ 0 := by
    have h1 : PowerSeries.X * (pw * r) = PowerSeries.X * 1 := by
      rw [mul_one, mul_left_comm, ← hr, ← hX]
    have h2 := mul_left_cancel₀ PowerSeries.X_ne_zero h1
    have h3 := congrArg PowerSeries.constantCoeff h2
    rw [map_mul, map_one] at h3
    exact right_ne_zero_of_mul_eq_one h3
  have hccder : PowerSeries.constantCoeff (PowerSeries.derivative k pϖ) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, hr,
      PowerSeries.coeff_succ_X_mul, Nat.cast_zero, zero_add, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hccr
  have hϖ' : Λ' (coef (KaehlerDifferential.D k F ϖ)) = HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative k pϖ) := by
    rw [← hcD, hpϖ, LaurentSeries.derivative_ofPowerSeries]
  have hcinv : (coef (KaehlerDifferential.D k F ϖ))⁻¹ ∈ v.toValuationSubring := by
    obtain ⟨q, hq⟩ := hinvps _ hccder
    exact hmem_of _ q (by rw [map_inv₀, hϖ', hq])
  have hdc_t₀ : v.differentialCoeff (KaehlerDifferential.D k F t₀) = (coef (KaehlerDifferential.D k F ϖ))⁻¹ := by
    have h1 : v.differentialCoeff v.dCoord =
        coef (KaehlerDifferential.D k F ϖ) * v.differentialCoeff (KaehlerDifferential.D k F t₀) := by
      rw [hdC]; exact hdc_eq _
    rw [v.differentialCoeff_dCoord] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D k F h) ∈ v.toValuationSubring := by
    intro h hh
    obtain ⟨p, hp⟩ := hps h hh
    have hc : coef (KaehlerDifferential.D k F h) ∈ v.toValuationSubring :=
      hmem_of _ (PowerSeries.derivative k p) (by rw [← hcD, hp, LaurentSeries.derivative_ofPowerSeries])
    rw [hdc_eq, hdc_t₀]
    exact mul_mem hc hcinv

  have hRES := fun h : F =>
    AlgebraicCurve.Place.algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D
      v hsurj hint Λ' hΛC hΛv ht₀ h

  have hG : ∀ (s g : 𝒰.A01), Λ.residue (s • KaehlerDifferential.D k 𝒰.A01 g) =
      kaehlerResidueTerm (Φ (s • KaehlerDifferential.D k 𝒰.A01 g)) (diagonalHom k F 1) v := by
    intro s g
    rw [Λ.residue_smul_D, hΦ]
    change _ = Algebra.trace k v.ResidueField
      (v.localResidue ((diagonalHom k F 1) v * v.differentialCoeff (ψ s • KaehlerDifferential.D k F (ψ g))))
    rw [diagonalHom_apply, one_mul, v.differentialCoeff_smul, hdc_eq (KaehlerDifferential.D k F (ψ g)),
      ← mul_assoc, ← hRES, htr, map_mul, hΛ', ← hcD, hΛ']

  have hGadd : ∀ a b : Ω[F⁄k], kaehlerResidueTerm (a + b) (diagonalHom k F 1) v =
      kaehlerResidueTerm a (diagonalHom k F 1) v + kaehlerResidueTerm b (diagonalHom k F 1) v := by
    intro a b
    change Algebra.trace k _ (v.localResidue (_ * v.differentialCoeff (a + b))) =
      Algebra.trace k _ (v.localResidue (_ * _)) + Algebra.trace k _ (v.localResidue (_ * _))
    rw [hdc_add, mul_add, map_add, map_add]
  have hG0 : kaehlerResidueTerm (0 : Ω[F⁄k]) (diagonalHom k F 1) v = 0 := by
    change Algebra.trace k _ (v.localResidue (_ * v.differentialCoeff 0)) = 0
    rw [v.differentialCoeff_zero, mul_zero, map_zero, map_zero]
  suffices H : ∀ s : 𝒰.A01, Λ.residue (s • η) = kaehlerResidueTerm (Φ (s • η)) (diagonalHom k F 1) v by
    simpa only [one_smul] using H 1
  have hη : η ∈ Submodule.span 𝒰.A01 (Set.range (KaehlerDifferential.D k 𝒰.A01)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hη using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact fun s => hG s g
  | zero => intro s; rw [smul_zero, map_zero, map_zero, hG0]
  | add x y _ _ hx hy => intro s; rw [smul_add, map_add, map_add, hGadd, hx, hy]
  | smul a x _ hx => intro s; rw [smul_smul]; exact hx (s * a)

end S_TwoChartCech_Cover_LaurentChart_residue_eq_kaehlerResidueTerm
end P2MW
export P2MW.S_TwoChartCech_Cover_LaurentChart_residue_eq_kaehlerResidueTerm (solution)
