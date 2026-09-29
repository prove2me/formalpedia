-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/39bdc9e9-6b59-5e31-af44-c9365b5de482

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_LevelNormalForm
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Theorems.Thm_ModularCurve_IsGamma1Point_existsUnique_variableChange_isNormalForm
import Theorems.Thm_WeierstrassCurve_exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range
import Theorems.Thm_ModularCurve_exists_map_eq_and_isGamma1Point_of_isGamma1Point_map
import Theorems.Thm_ModularCurve_IsGamma1Point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

p2m_open "ModularCurve WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ map b₂ a₄ a₂ a₆ reduction map_Δ b₆ Δ VariableChange map_variableChange b₄ jOfUnit isUnit_Δ_map isUnit_Δ_variableChange exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range"
namespace GoodModelG1
p2m_open "WeierstrassCurve"

theorem exists_unit_of_trace {R₀ K A' K' : Type*} [CommRing R₀] [Field K] [Algebra R₀ K]
    [CommRing A'] [Nontrivial A'] [Field K'] [Algebra A' K'] [Algebra K K']
    (hinj : Function.Injective (algebraMap R₀ K)) (hinj' : Function.Injective (algebraMap A' K'))
    (hA'K : ∀ x : K, algebraMap K K' x ∈ Set.range (algebraMap A' K') → x ∈ Set.range (algebraMap R₀ K))
    (z : K) (w : A'ˣ) (hz : algebraMap K K' z = algebraMap A' K' w) :
    ∃ r : R₀ˣ, algebraMap R₀ K r = z := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hz
    exact w.ne_zero (hinj' (by rw [map_zero]; exact hz.symm))
  obtain ⟨r, hr⟩ := hA'K z ⟨w, hz.symm⟩
  obtain ⟨s, hs⟩ := hA'K z⁻¹ ⟨((w⁻¹ : A'ˣ) : A'), by
    rw [map_inv₀, hz]
    exact (eq_inv_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one]))⟩
  have hrs : r * s = 1 := hinj (by rw [map_mul, hr, hs, mul_inv_cancel₀ hz0, map_one])
  exact ⟨Units.mkOfMulEqOne r s hrs, hr⟩

theorem exists_eq_map_of_map_eq_map {R₀ K A' K' : Type*} [CommRing R₀] [CommRing K] [Algebra R₀ K]
    [CommRing A'] [CommRing K'] [Algebra A' K'] [Algebra K K']
    (hA'K : ∀ x : K, algebraMap K K' x ∈ Set.range (algebraMap A' K') → x ∈ Set.range (algebraMap R₀ K))
    (V : WeierstrassCurve K) (V' : WeierstrassCurve A') (h : V.map (algebraMap K K') = V'.map (algebraMap A' K')) :
    ∃ V₀ : WeierstrassCurve R₀, V = V₀.map (algebraMap R₀ K) := by
  have h1 : algebraMap K K' V.a₁ = algebraMap A' K' V'.a₁ := by simpa [WeierstrassCurve.map] using congrArg WeierstrassCurve.a₁ h
  have h2 : algebraMap K K' V.a₂ = algebraMap A' K' V'.a₂ := by simpa [WeierstrassCurve.map] using congrArg WeierstrassCurve.a₂ h
  have h3 : algebraMap K K' V.a₃ = algebraMap A' K' V'.a₃ := by simpa [WeierstrassCurve.map] using congrArg WeierstrassCurve.a₃ h
  have h4 : algebraMap K K' V.a₄ = algebraMap A' K' V'.a₄ := by simpa [WeierstrassCurve.map] using congrArg WeierstrassCurve.a₄ h
  have h6 : algebraMap K K' V.a₆ = algebraMap A' K' V'.a₆ := by simpa [WeierstrassCurve.map] using congrArg WeierstrassCurve.a₆ h
  obtain ⟨b₁, hb₁⟩ := hA'K _ ⟨_, h1.symm⟩
  obtain ⟨b₂, hb₂⟩ := hA'K _ ⟨_, h2.symm⟩
  obtain ⟨b₃, hb₃⟩ := hA'K _ ⟨_, h3.symm⟩
  obtain ⟨b₄, hb₄⟩ := hA'K _ ⟨_, h4.symm⟩
  obtain ⟨b₆, hb₆⟩ := hA'K _ ⟨_, h6.symm⟩
  exact ⟨⟨b₁, b₂, b₃, b₄, b₆⟩, by ext <;> simp [WeierstrassCurve.map, hb₁, hb₂, hb₃, hb₄, hb₆]⟩

end WeierstrassCurve.GoodModelG1

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (W : WeierstrassCurve K) (hΔ : IsUnit W.Δ)
    (hj : W.jOfUnit hΔ ∈ Set.range (algebraMap R₀ K))
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsGamma1Point W ℓ D) :
    ∃ (C : WeierstrassCurve.VariableChange K) (W₀ : WeierstrassCurve R₀),
      IsUnit W₀.Δ ∧ C • W = W₀.map (algebraMap R₀ K) := by
  classical
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K

  obtain ⟨K', _, _, _, A', _, _, _, _, _, f, hfK, hA'K, C', W', hΔ', hC'⟩ :=
    WeierstrassCurve.exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range W hΔ hj
  have hinj' : Function.Injective (algebraMap A' K') := IsFractionRing.injective A' K'
  have hfK' : ∀ r : R₀, algebraMap A' K' (f r) = algebraMap K K' (algebraMap R₀ K r) :=
    fun r => RingHom.congr_fun hfK r
  set φ : K →+* K' := algebraMap K K' with hφ
  set ψ : A' →+* K' := algebraMap A' K' with hψ

  have hℓA' : IsUnit ((ℓ : ℕ) : A') := by simpa using hℓ.map f
  have hℓK : IsUnit ((ℓ : ℕ) : K) := by simpa using hℓ.map (algebraMap R₀ K)
  have hℓK' : IsUnit ((ℓ : ℕ) : K') := by simpa using hℓK.map φ

  have hDK' : ModularCurve.IsGamma1Point (W'.map ψ) ℓ ((D.map φ).variableChange C') := by
    rw [← hC']; exact (hD.map φ).variableChange C'
  obtain ⟨D₁, hD₁map, hD₁⟩ :=
    ModularCurve.exists_map_eq_and_isGamma1Point_of_isGamma1Point_map W' ℓ hℓA' _ hDK'

  have huK : IsUnit ((ℓ : K) * W.Δ) := by
    have : IsUnit (ℓ : K) := by exact_mod_cast hℓK
    exact this.mul hΔ
  have huA' : IsUnit ((ℓ : A') * W'.Δ) := by
    have : IsUnit (ℓ : A') := by exact_mod_cast hℓA'
    exact this.mul hΔ'
  have huK' : IsUnit ((ℓ : K') * (W.map φ).Δ) := by
    have : IsUnit (ℓ : K') := by exact_mod_cast hℓK'
    exact this.mul (W.isUnit_Δ_map φ hΔ)
  obtain ⟨CK, hNK⟩ := (ModularCurve.IsGamma1Point.existsUnique_variableChange_isNormalForm ℓ hℓ5 W huK D hD).exists
  obtain ⟨CA, hNA⟩ := (ModularCurve.IsGamma1Point.existsUnique_variableChange_isNormalForm ℓ hℓ5 W' huA' D₁ hD₁).exists

  have hN1 : ModularCurve.IsNormalForm ℓ ((CK.map φ) • W.map φ) ((D.map φ).variableChange (CK.map φ)) := by
    have h := hNK.map φ
    rwa [← WeierstrassCurve.map_variableChange, ModularCurve.LevelPData.map_variableChange] at h
  have hN2 : ModularCurve.IsNormalForm ℓ ((CA.map ψ * C') • W.map φ) ((D.map φ).variableChange (CA.map ψ * C')) := by
    have h := hNA.map ψ
    rw [← WeierstrassCurve.map_variableChange, ModularCurve.LevelPData.map_variableChange, hD₁map, ← hC',
      ← mul_smul, ← ModularCurve.LevelPData.variableChange_mul] at h
    exact h
  have hCeq : CK.map φ = CA.map ψ * C' :=
    (ModularCurve.IsGamma1Point.existsUnique_variableChange_isNormalForm ℓ hℓ5 (W.map φ) huK' (D.map φ)
      (hD.map φ)).unique hN1 hN2

  have hcurves : (CK • W).map φ = (CA • W').map ψ := by
    rw [← WeierstrassCurve.map_variableChange, hCeq, mul_smul, hC', WeierstrassCurve.map_variableChange]

  obtain ⟨W₀, hW₀⟩ := WeierstrassCurve.GoodModelG1.exists_eq_map_of_map_eq_map hA'K (CK • W) (CA • W') hcurves
  have hΔA : IsUnit (CA • W').Δ := W'.isUnit_Δ_variableChange CA hΔ'
  obtain ⟨r, hr⟩ := WeierstrassCurve.GoodModelG1.exists_unit_of_trace hinj hinj' hA'K ((CK • W).Δ) hΔA.unit (by
    rw [IsUnit.unit_spec, ← WeierstrassCurve.map_Δ, ← WeierstrassCurve.map_Δ, hcurves])
  refine ⟨CK, W₀, ?_, hW₀⟩
  have hΔ₀ : algebraMap R₀ K W₀.Δ = algebraMap R₀ K r := by
    rw [hr, hW₀, WeierstrassCurve.map_Δ]
  rw [hinj hΔ₀]
  exact Units.isUnit r

end S_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isGamma1Point_of_jOfUnit_mem_range (solution)
