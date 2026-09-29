-- Prove2me | solution 1 for WeierstrassCurve.exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1cf27041-da5e-50fd-852b-277cfd14d64d

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
import Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

open WeierstrassCurve

theorem plumb1_exists_valuationSubring_of_dvr
    (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    (K : Type u) [Field K] [Algebra R₀ K] [IsFractionRing R₀ K] :
    ∃ W₀ : ValuationSubring K, IsDiscreteValuationRing ↥W₀ ∧ ∀ x : K, x ∈ W₀ ↔ x ∈ Set.range (algebraMap R₀ K) := by
  classical
  let v := ValuationRing.valuation R₀ K
  refine ⟨v.valuationSubring, ?_, fun x => ?_⟩
  swap
  · rw [Valuation.mem_valuationSubring_iff]
    exact (ValuationRing.mem_integer_iff R₀ K x)
  ·
    have hmem : ∀ x : K, x ∈ v.valuationSubring ↔ ∃ a : R₀, algebraMap R₀ K a = x := fun x => by
      rw [Valuation.mem_valuationSubring_iff]; exact (ValuationRing.mem_integer_iff R₀ K x)
    have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
    let e : R₀ →+* ↥(v.valuationSubring) := (algebraMap R₀ K).codRestrict _ (fun a => (hmem _).mpr ⟨a, rfl⟩)
    have he : Function.Surjective e := by
      rintro ⟨x, hx⟩; obtain ⟨a, rfl⟩ := (hmem x).mp hx; exact ⟨a, rfl⟩
    have heinj : Function.Injective e := fun a b h => hinj (by
      have := congrArg (fun w : ↥(v.valuationSubring) => (w : K)) h; exact this)
    haveI : IsPrincipalIdealRing ↥(v.valuationSubring) := IsPrincipalIdealRing.of_surjective e he
    refine { not_a_field' := ?_ }

    intro hbot
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
    have hϖmem : e ϖ ∈ IsLocalRing.maximalIdeal ↥(v.valuationSubring) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hϖ.not_isUnit

      obtain ⟨u, hu⟩ := hu
      obtain ⟨b, hb⟩ := he ((u⁻¹ : (↥(v.valuationSubring))ˣ) : ↥(v.valuationSubring))
      refine ⟨⟨ϖ, b, heinj ?_, heinj ?_⟩, rfl⟩
      · rw [map_mul, hb, ← hu, Units.mul_inv, map_one]
      · rw [map_mul, hb, ← hu, Units.inv_mul, map_one]
    rw [hbot, Ideal.mem_bot] at hϖmem
    exact hϖ.ne_zero (heinj (by rw [hϖmem, map_zero]))

theorem plumb2_trace_of_dominates
    {K : Type u} [Field K] (W₀ : ValuationSubring K)
    {L : Type u} [Field L] [Algebra K L] (V : ValuationSubring L)
    (hVW : ∀ x : K, x ∈ W₀ → algebraMap K L x ∈ V)
    (hVm : ∀ x : ↥W₀, x ∈ IsLocalRing.maximalIdeal ↥W₀ → algebraMap K L (x : K) ∈ V.nonunits)
    (x : K) (hx : algebraMap K L x ∈ Set.range (algebraMap ↥V L)) : x ∈ W₀ := by
  classical
  obtain ⟨v, hv⟩ := hx
  by_contra hxW
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hxW (zero_mem W₀)
  have hinv : x⁻¹ ∈ W₀ := by
    rcases W₀.mem_or_inv_mem x with h | h
    · exact absurd h hxW
    · exact h
  have hmax : (⟨x⁻¹, hinv⟩ : ↥W₀) ∈ IsLocalRing.maximalIdeal ↥W₀ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu⟩ := hu
    apply hxW
    have hcoe : ((u : ↥W₀) : K) = x⁻¹ := by rw [hu]
    have hinv' : (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : K) = x := by
      have h1 : (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : K) * x⁻¹ = 1 := by
        rw [← hcoe, ← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl
      calc (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : K) = (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : K) * x⁻¹ * x := by
              rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one]
        _ = x := by rw [h1, one_mul]
    rw [← hinv']
    exact ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2
  have hnu := hVm _ hmax
  rw [ValuationSubring.mem_nonunits_iff] at hnu

  have hy : algebraMap K L x = (v : L) := hv.symm
  have hvle : V.valuation (v : L) ≤ 1 := V.valuation_le_one v
  have hy0 : algebraMap K L x ≠ 0 := by rw [map_ne_zero]; exact hx0
  rw [map_inv₀, hy, map_inv₀] at hnu
  have hv0 : V.valuation (v : L) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; rw [← hy]; exact hy0

  have : (1 : _) < V.valuation (v : L) := by
    rwa [inv_lt_one₀ (zero_lt_iff.mpr hv0)] at hnu
  exact absurd hvle (not_le.mpr this)

theorem isUnit_two_or_isUnit_three (R₀ : Type u) [CommRing R₀] [IsLocalRing R₀] :
    IsUnit ((2 : ℕ) : R₀) ∨ IsUnit ((3 : ℕ) : R₀) := by
  by_contra h
  push_neg at h
  have h2 : ((2 : ℕ) : R₀) ∈ IsLocalRing.maximalIdeal R₀ := (IsLocalRing.mem_maximalIdeal _).mpr h.1
  have h3 : ((3 : ℕ) : R₀) ∈ IsLocalRing.maximalIdeal R₀ := (IsLocalRing.mem_maximalIdeal _).mpr h.2
  have h1 : (1 : R₀) ∈ IsLocalRing.maximalIdeal R₀ := by
    have h32 := Ideal.sub_mem _ h3 h2
    have e : ((3 : ℕ) : R₀) - ((2 : ℕ) : R₀) = 1 := by norm_num
    rwa [e] at h32
  exact (IsLocalRing.maximalIdeal.isMaximal R₀).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W : WeierstrassCurve K) (hΔ : IsUnit W.Δ)
    (hj : W.jOfUnit hΔ ∈ Set.range (algebraMap R₀ K)) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A' K') (_ : IsFractionRing A' K') (f : R₀ →+* A'),
      (algebraMap A' K').comp f = (algebraMap K K').comp (algebraMap R₀ K) ∧
      (∀ x : K, algebraMap K K' x ∈ Set.range (algebraMap A' K') → x ∈ Set.range (algebraMap R₀ K)) ∧
      ∃ (C' : WeierstrassCurve.VariableChange K') (W' : WeierstrassCurve A'),
        IsUnit W'.Δ ∧ C' • (W.map (algebraMap K K')) = W'.map (algebraMap A' K') := by
  classical
  haveI hE : W.IsElliptic := ⟨hΔ⟩

  obtain ⟨r, hr⟩ := hj
  have hjr : W.j = algebraMap R₀ K r := by rw [← W.jOfUnit_eq_j hΔ]; exact hr.symm

  obtain ⟨W₀, hW₀, hW₀mem⟩ := plumb1_exists_valuationSubring_of_dvr R₀ K
  have hmemW : ∀ s : R₀, algebraMap R₀ K s ∈ W₀ := fun s => (hW₀mem _).mpr ⟨s, rfl⟩
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K

  let Ω := AlgebraicClosure K
  have package : ∀ (S : IntermediateField K Ω), FiniteDimensional K S →
      (∀ (A : ValuationSubring S), (∀ s : R₀, algebraMap K S (algebraMap R₀ K s) ∈ A) →
          algebraMap K S W.j ∈ A →
          ∃ (W' : WeierstrassCurve A) (κ : VariableChange S), κ • W.baseChange S = W'.map A.subtype ∧ IsUnit W'.Δ) →
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
        (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
        (_ : Algebra A' K') (_ : IsFractionRing A' K') (f : R₀ →+* A'),
        (algebraMap A' K').comp f = (algebraMap K K').comp (algebraMap R₀ K) ∧
        (∀ x : K, algebraMap K K' x ∈ Set.range (algebraMap A' K') → x ∈ Set.range (algebraMap R₀ K)) ∧
        ∃ (C' : WeierstrassCurve.VariableChange K') (W' : WeierstrassCurve A'),
          IsUnit W'.Δ ∧ C' • (W.map (algebraMap K K')) = W'.map (algebraMap A' K') := by
    intro S hfin supplier
    haveI : FiniteDimensional K S := hfin
    obtain ⟨V, hV, hVW, hVm⟩ :=
      ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional (F := K) (E := ↥S) W₀ hW₀
    have hRV : ∀ s : R₀, algebraMap K S (algebraMap R₀ K s) ∈ V := fun s => hVW _ (hmemW s)
    have hjV : algebraMap K S W.j ∈ V := by rw [hjr]; exact hRV r
    obtain ⟨W', κ, hκ, hΔ'⟩ := supplier V hRV hjV
    let f : R₀ →+* ↥V := ((algebraMap K ↥S).comp (algebraMap R₀ K)).codRestrict V hRV
    haveI : IsDiscreteValuationRing ↥V := hV
    refine ⟨↥S, inferInstance, inferInstance, hfin, ↥V, inferInstance, inferInstance, hV, inferInstance, inferInstance, f,
      ?_, ?_, κ, W', hΔ', ?_⟩
    · ext s; rfl
    · intro x hx
      exact (hW₀mem x).mp (plumb2_trace_of_dominates W₀ V hVW hVm x hx)
    · simp [WeierstrassCurve.baseChange] at hκ
      exact hκ

  rcases isUnit_two_or_isUnit_three R₀ with h2 | h3
  ·
    have h2K : (2 : K) ≠ 0 := by
      have h := (h2.map (algebraMap R₀ K)).ne_zero
      rwa [map_natCast, Nat.cast_ofNat] at h
    obtain ⟨S, hfin, -, hS⟩ :=
      WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero (Ω := Ω) W h2K
    refine package S hfin fun A hRA hjA => ?_
    have h2A : IsUnit (2 : ↥A) := by
      have h := h2.map (((algebraMap K ↥S).comp (algebraMap R₀ K)).codRestrict A hRA)
      rwa [map_natCast, Nat.cast_ofNat] at h
    obtain ⟨W', κ, hκ, hΔ', -⟩ := hS S le_rfl A h2A hjA
    exact ⟨W', κ, hκ, hΔ'⟩
  ·
    have h3K : (3 : K) ≠ 0 := by
      have h := (h3.map (algebraMap R₀ K)).ne_zero
      rwa [map_natCast, Nat.cast_ofNat] at h
    obtain ⟨S, hfin, -, hS⟩ :=
      WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero (Ω := Ω) W h3K
    refine package S hfin fun A hRA hjA => ?_
    have h3A : IsUnit (3 : ↥A) := by
      have h := h3.map (((algebraMap K ↥S).comp (algebraMap R₀ K)).codRestrict A hRA)
      rwa [map_natCast, Nat.cast_ofNat] at h
    obtain ⟨W', κ, hκ, hΔ', -⟩ := hS S le_rfl A h3A hjA
    exact ⟨W', κ, hκ, hΔ'⟩

end S_WeierstrassCurve_exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range
end P2MW
export P2MW.S_WeierstrassCurve_exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range (solution)
