-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/46f8d1c5-1fa6-535c-b71b-c58d1d199936

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_map_short_of_isUnit_two_three
import Theorems.Thm_WeierstrassCurve_discr_dvd_pow_of_jOfUnit_mem_range_short
import Theorems.Thm_IsDiscreteValuationRing_exists_dvr_extension_pow_eq
import Theorems.Thm_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
import Theorems.Thm_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Theorems.Thm_ModularCurve_exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "ΨSq_one map_map map b₂ variableChange_a₃ variableChange_a₆ variableChange_a₂ map_Δ b₆ b₈ variableChange_a₁ variableChange_a₄ Δ VariableChange Φ_one j b₄ jOfUnit jOfUnit_variableChange isUnit_Δ_variableChange exists_variableChange_smul_eq_map_short_of_isUnit_two_three discr_dvd_pow_of_jOfUnit_mem_range_short mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd"
namespace GoodModel
p2m_open "WeierstrassCurve"

open ModularCurve

theorem dvd_of_pow_dvd_pow {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A] {x y : A} {k : ℕ} (hk : k ≠ 0)
    (h : y ^ k ∣ x ^ k) : y ∣ x := by
  rcases ValuationRing.dvd_total y x with hyx | ⟨t, rfl⟩
  · exact hyx
  ·
    by_cases hx : x = 0
    · simp [hx]
    rw [mul_pow] at h
    have : t ^ k ∣ 1 := by
      have hxk : x ^ k ≠ 0 := pow_ne_zero _ hx
      obtain ⟨c, hc⟩ := h
      refine ⟨c, mul_left_cancel₀ hxk ?_⟩
      rw [mul_one, ← mul_assoc]
      exact hc
    have ht : IsUnit t := isUnit_of_dvd_one (dvd_trans (dvd_pow_self t hk) this)
    exact ⟨↑ht.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem isUnit_sub_of_isUnit_indepElt {T : Type*} [CommRing T] (W : WeierstrassCurve T) {ℓ : ℕ} (hℓ3 : 3 ≤ ℓ)
    {x₀ x : T} (h : IsUnit (ModularCurve.indepElt W ℓ x₀ x)) : IsUnit (x - x₀) := by
  unfold ModularCurve.indepElt at h
  have h1 : 1 ∈ Finset.Icc 1 ((ℓ - 1) / 2) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  rw [← Finset.mul_prod_erase _ _ h1] at h
  have h' := isUnit_of_mul_isUnit_left h
  simpa [WeierstrassCurve.ΨSq_one, WeierstrassCurve.Φ_one] using h'

theorem jOfUnit_eq_of_eq_smul {K : Type*} [CommRing K] (W V : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
    (hV : V = C • W) (hW : IsUnit W.Δ) (hV' : IsUnit V.Δ) : V.jOfUnit hV' = W.jOfUnit hW := by
  subst hV
  exact W.jOfUnit_variableChange C hW hV'

theorem mul_eq_of_pow_eq_pow_mul_unit {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {π : R₀} (hπ : Irreducible π) {y : R₀} (hy : y ≠ 0) {k n : ℕ} (r : R₀ˣ) (h : y ^ k = π ^ n * r) :
    k ∣ n := by
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ

  have : ((v ^ k : R₀ˣ) : R₀) * π ^ (e * k) = (r : R₀) * π ^ n := by
    rw [Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, ← hv, h, mul_comm]
  have hke := IsDiscreteValuationRing.unit_mul_pow_congr_pow hπ hπ _ _ _ _ this
  exact ⟨e, by rw [mul_comm]; exact hke.symm⟩

theorem Δ_short {R : Type*} [CommRing R] (a b : R) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R).Δ = -64 * a ^ 3 - 432 * b ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem smul_short_eq_of_eq_pow_mul {L : Type*} [Field L] (ϖ : L) (hϖ : ϖ ≠ 0) (n : ℕ) (a b a' b' : L)
    (ha : a = ϖ ^ (4 * n) * a') (hb : b = ϖ ^ (6 * n) * b') :
    (⟨Units.mk0 (ϖ ^ n) (pow_ne_zero _ hϖ), 0, 0, 0⟩ : WeierstrassCurve.VariableChange L) •
        (⟨0, 0, 0, a, b⟩ : WeierstrassCurve L) = ⟨0, 0, 0, a', b'⟩ := by
  have hϖn : ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ
  ext
  · simp [WeierstrassCurve.variableChange_a₁]
  · simp [WeierstrassCurve.variableChange_a₂]
  · simp [WeierstrassCurve.variableChange_a₃]
  · rw [WeierstrassCurve.variableChange_a₄]
    simp only [mul_zero, zero_mul, sub_zero, add_zero, Units.val_inv_eq_inv_val, Units.val_mk0, ha]
    field_simp
    ring
  · rw [WeierstrassCurve.variableChange_a₆]
    simp only [mul_zero, zero_mul, sub_zero, add_zero, Units.val_inv_eq_inv_val, Units.val_mk0, hb]
    field_simp
    ring

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

end WeierstrassCurve.GoodModel

set_option maxHeartbeats 3200000 in
theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (h2 : IsUnit ((2 : ℕ) : R₀)) (h3 : IsUnit ((3 : ℕ) : R₀))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓ : IsUnit ((ℓ : ℕ) : R₀))
    (W : WeierstrassCurve K) (hΔ : IsUnit W.Δ)
    (hj : W.jOfUnit hΔ ∈ Set.range (algebraMap R₀ K))
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    ∃ (C : WeierstrassCurve.VariableChange K) (W₀ : WeierstrassCurve R₀),
      IsUnit W₀.Δ ∧ C • W = W₀.map (algebraMap R₀ K) := by
  classical
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
  have hℓodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)

  obtain ⟨C₁, a, b, hC₁⟩ := WeierstrassCurve.exists_variableChange_smul_eq_map_short_of_isUnit_two_three h2 h3 W
  have hΔ₁K : IsUnit ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)).Δ := by
    rw [← hC₁]; exact W.isUnit_Δ_variableChange C₁ hΔ
  have hΔ₁ : (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).Δ ≠ 0 := by
    intro h0; apply hΔ₁K.ne_zero; rw [WeierstrassCurve.map_Δ, h0, map_zero]

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  obtain ⟨n, ε, hnε⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hΔ₁ hπ
  rw [WeierstrassCurve.GoodModel.Δ_short] at hnε

  have hj₁ : ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)).jOfUnit hΔ₁K ∈ Set.range (algebraMap R₀ K) := by
    rw [WeierstrassCurve.GoodModel.jOfUnit_eq_of_eq_smul W _ C₁ hC₁.symm hΔ hΔ₁K]; exact hj
  obtain ⟨⟨ca, hca⟩, ⟨cb, hcb⟩⟩ := WeierstrassCurve.discr_dvd_pow_of_jOfUnit_mem_range_short h2 h3 a b hΔ₁K hj₁
  rw [WeierstrassCurve.GoodModel.Δ_short] at hca hcb

  rw [hnε] at hca hcb

  have h12 : IsUnit ((12 : ℕ) : R₀) := by
    have e : ((12 : ℕ) : R₀) = ((2 : ℕ) : R₀) ^ 2 * ((3 : ℕ) : R₀) := by push_cast; norm_num
    rw [e]; exact (h2.pow 2).mul h3
  obtain ⟨K', _, _, A', _, _, _, _, _, f, hfK, hA'K, ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_dvr_extension_pow_eq (K := K) 12 h12 (by norm_num) π hπ.ne_zero
  have hinj' : Function.Injective (algebraMap A' K') := IsFractionRing.injective A' K'
  have hfK' : ∀ r : R₀, algebraMap A' K' (f r) = algebraMap K K' (algebraMap R₀ K r) :=
    fun r => RingHom.congr_fun hfK r
  have hfπ : f π = ϖ ^ 12 := hinj' (by rw [hfK', map_pow, hϖ])
  have hιϖ0 : algebraMap A' K' ϖ ≠ 0 := by
    intro h0
    have h1 : algebraMap K K' (algebraMap R₀ K π) = 0 := by rw [← hϖ, h0, zero_pow (by norm_num)]
    exact hπ.ne_zero (hinj ((algebraMap K K').injective (by rw [h1, map_zero, map_zero])))
  have hϖ0 : ϖ ≠ 0 := fun h0 => hιϖ0 (by rw [h0, map_zero])

  have hfa : ϖ ^ (4 * n) ∣ f a := by
    refine WeierstrassCurve.GoodModel.dvd_of_pow_dvd_pow (k := 3) (by norm_num) ⟨f ((ε : R₀) * ca), ?_⟩
    rw [← map_pow, hca, map_mul, map_mul, map_mul, map_pow, hfπ, ← pow_mul, ← pow_mul]
    ring
  have hfb : ϖ ^ (6 * n) ∣ f b := by
    refine WeierstrassCurve.GoodModel.dvd_of_pow_dvd_pow (k := 2) (by norm_num) ⟨f ((ε : R₀) * cb), ?_⟩
    rw [← map_pow, hcb, map_mul, map_mul, map_mul, map_pow, hfπ, ← pow_mul, ← pow_mul]
    ring
  obtain ⟨a', ha'⟩ := hfa
  obtain ⟨b', hb'⟩ := hfb
  have hΔ' : (⟨0, 0, 0, a', b'⟩ : WeierstrassCurve A').Δ = f (ε : R₀) := by
    have h1 : f (-64 * a ^ 3 - 432 * b ^ 2) = f ((ε : R₀) * π ^ n) := by rw [hnε]
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, ha', hb', map_mul, map_pow, hfπ, ← pow_mul] at h1
    rw [WeierstrassCurve.GoodModel.Δ_short]
    have hϖ12 : (ϖ ^ (12 * n)) ≠ 0 := pow_ne_zero _ hϖ0
    apply mul_left_cancel₀ hϖ12
    simp only [map_neg, map_ofNat] at h1
    linear_combination h1
  have hΔ'u : IsUnit (⟨0, 0, 0, a', b'⟩ : WeierstrassCurve A').Δ := by rw [hΔ']; exact (Units.isUnit ε).map f

  have hD₁ : ModularCurve.IsLevelPStructure ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)) ℓ
      (D.variableChange C₁) := by
    rw [← hC₁]; exact ModularCurve.IsLevelPStructure.variableChange hD C₁
  have hD₁' := hD₁.map (algebraMap K K')
  rw [WeierstrassCurve.map_map] at hD₁'
  have hcurve : ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map ((algebraMap K K').comp (algebraMap R₀ K))) =
      (⟨0, 0, 0, algebraMap A' K' (f a), algebraMap A' K' (f b)⟩ : WeierstrassCurve K') := by
    ext <;> simp [WeierstrassCurve.map, hfK']
  rw [hcurve] at hD₁'
  have hsmul := WeierstrassCurve.GoodModel.smul_short_eq_of_eq_pow_mul (algebraMap A' K' ϖ) hιϖ0 n
    (algebraMap A' K' (f a)) (algebraMap A' K' (f b)) (algebraMap A' K' a') (algebraMap A' K' b')
    (by rw [ha', map_mul, map_pow]) (by rw [hb', map_mul, map_pow])
  have hD' := ModularCurve.IsLevelPStructure.variableChange hD₁'
    (⟨Units.mk0 ((algebraMap A' K' ϖ) ^ n) (pow_ne_zero _ hιϖ0), 0, 0, 0⟩ : WeierstrassCurve.VariableChange K')
  rw [hsmul] at hD'
  have hW'map : (⟨0, 0, 0, algebraMap A' K' a', algebraMap A' K' b'⟩ : WeierstrassCurve K') =
      (⟨0, 0, 0, a', b'⟩ : WeierstrassCurve A').map (algebraMap A' K') := by
    ext <;> simp [WeierstrassCurve.map]
  rw [hW'map] at hD'

  have hℓ' : IsUnit ((ℓ : ℕ) : A') := by simpa using hℓ.map f
  obtain ⟨D₀, hD₀map, hD₀⟩ :=
    ModularCurve.exists_map_eq_and_isLevelPStructure_of_isLevelPStructure_map _ hΔ'u ℓ hℓ' _ hD'
  have hxunit : IsUnit (D₀.xQ - D₀.xP) :=
    WeierstrassCurve.GoodModel.isUnit_sub_of_isUnit_indepElt _ hℓ3 hD₀.isUnit_indepElt_PQ
  have hyunit : IsUnit D₀.yP := by
    have h := WeierstrassCurve.isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd _ hΔ'u hℓodd
      hD₀.equation_P hD₀.preΨ_P
    simp only [mul_zero, zero_mul, add_zero] at h
    exact isUnit_of_mul_isUnit_right h

  have hyP : algebraMap A' K' D₀.yP =
      ((Units.mk0 ((algebraMap A' K' ϖ) ^ n) (pow_ne_zero _ hιϖ0))⁻¹ : K'ˣ) ^ 3 *
        (algebraMap K K' (D.variableChange C₁).yP - 0 * (algebraMap K K' (D.variableChange C₁).xP - 0) - 0) := by
    have := congrArg ModularCurve.LevelPData.yP hD₀map
    simpa [ModularCurve.LevelPData.map_yP, ModularCurve.LevelPData.variableChange_yP] using this
  have hxP : algebraMap A' K' D₀.xP =
      ((Units.mk0 ((algebraMap A' K' ϖ) ^ n) (pow_ne_zero _ hιϖ0))⁻¹ : K'ˣ) ^ 2 *
        (algebraMap K K' (D.variableChange C₁).xP - 0) := by
    have := congrArg ModularCurve.LevelPData.xP hD₀map
    simpa [ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.variableChange_xP] using this
  have hxQ : algebraMap A' K' D₀.xQ =
      ((Units.mk0 ((algebraMap A' K' ϖ) ^ n) (pow_ne_zero _ hιϖ0))⁻¹ : K'ˣ) ^ 2 *
        (algebraMap K K' (D.variableChange C₁).xQ - 0) := by
    have := congrArg ModularCurve.LevelPData.xQ hD₀map
    simpa [ModularCurve.LevelPData.map_xQ, ModularCurve.LevelPData.variableChange_xQ] using this
  set y₁ : K := (D.variableChange C₁).yP with hy₁
  set d₁ : K := (D.variableChange C₁).xQ - (D.variableChange C₁).xP with hd₁
  have hy₁' : algebraMap K K' y₁ = (algebraMap A' K' ϖ) ^ (3 * n) * algebraMap A' K' D₀.yP := by
    rw [hyP]; simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0]; field_simp; ring
  have hd₁' : algebraMap K K' d₁ = (algebraMap A' K' ϖ) ^ (2 * n) * algebraMap A' K' (D₀.xQ - D₀.xP) := by
    rw [map_sub (algebraMap A' K'), hxP, hxQ, hd₁, map_sub]
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0]; field_simp; ring
  have hπK0 : algebraMap R₀ K π ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ.ne_zero

  obtain ⟨ry, hry⟩ := WeierstrassCurve.GoodModel.exists_unit_of_trace hinj hinj' hA'K
    (y₁ ^ 4 / (algebraMap R₀ K π) ^ n) (hyunit.unit ^ 4) (by
      rw [map_div₀, map_pow, map_pow, hy₁', ← hϖ, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]
      field_simp; ring)
  obtain ⟨rd, hrd⟩ := WeierstrassCurve.GoodModel.exists_unit_of_trace hinj hinj' hA'K
    (d₁ ^ 6 / (algebraMap R₀ K π) ^ n) (hxunit.unit ^ 6) (by
      rw [map_div₀, map_pow, map_pow, hd₁', ← hϖ, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]
      field_simp; ring)

  obtain ⟨⟨xP₀, hxP₀⟩, ⟨yP₀, hyP₀⟩⟩ := WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀) ℓ hℓ _ _ hD₁.equation_P hD₁.preΨ_P
  obtain ⟨⟨xQ₀, hxQ₀⟩, -⟩ := WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀) ℓ hℓ _ _ hD₁.equation_Q hD₁.preΨ_Q
  have hy4 : yP₀ ^ 4 = π ^ n * ry := by
    apply hinj
    rw [map_pow, hyP₀, map_mul, map_pow, hry, ← hy₁, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero _ hπK0)]
  have hd6 : (xQ₀ - xP₀) ^ 6 = π ^ n * rd := by
    apply hinj
    rw [map_pow, map_sub, hxP₀, hxQ₀, map_mul, map_pow, hrd, ← hd₁, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero _ hπK0)]
  have hyP₀0 : yP₀ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by norm_num)] at hy4
    exact (Units.ne_zero ry) ((mul_eq_zero.mp hy4.symm).resolve_left (pow_ne_zero _ hπ.ne_zero))
  have hd₀0 : xQ₀ - xP₀ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by norm_num)] at hd6
    exact (Units.ne_zero rd) ((mul_eq_zero.mp hd6.symm).resolve_left (pow_ne_zero _ hπ.ne_zero))
  have h4 : 4 ∣ n := WeierstrassCurve.GoodModel.mul_eq_of_pow_eq_pow_mul_unit hπ hyP₀0 ry hy4
  have h6 : 6 ∣ n := WeierstrassCurve.GoodModel.mul_eq_of_pow_eq_pow_mul_unit hπ hd₀0 rd hd6
  obtain ⟨m, hm⟩ : ∃ m, n = 12 * m := by obtain ⟨i, hi⟩ := h4; obtain ⟨j, hj⟩ := h6; exact ⟨n / 12, by omega⟩

  subst hm
  have hda' : π ^ (4 * m) ∣ a := by
    refine WeierstrassCurve.GoodModel.dvd_of_pow_dvd_pow (k := 3) (by norm_num) ⟨(ε : R₀) * ca, ?_⟩
    rw [hca]; ring
  have hdb' : π ^ (6 * m) ∣ b := by
    refine WeierstrassCurve.GoodModel.dvd_of_pow_dvd_pow (k := 2) (by norm_num) ⟨(ε : R₀) * cb, ?_⟩
    rw [hcb]; ring
  obtain ⟨a₀, ha₀⟩ := hda'
  obtain ⟨b₀, hb₀⟩ := hdb'
  have hΔ₀ : (⟨0, 0, 0, a₀, b₀⟩ : WeierstrassCurve R₀).Δ = ε := by
    rw [WeierstrassCurve.GoodModel.Δ_short]
    apply mul_left_cancel₀ (pow_ne_zero (12 * m) hπ.ne_zero)
    rw [ha₀, hb₀] at hnε
    linear_combination hnε
  refine ⟨⟨Units.mk0 ((algebraMap R₀ K π) ^ m) (pow_ne_zero _ hπK0), 0, 0, 0⟩ * C₁, ⟨0, 0, 0, a₀, b₀⟩,
    by rw [hΔ₀]; exact Units.isUnit ε, ?_⟩
  rw [mul_smul, hC₁]
  have hmapW₁ : ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)) =
      ⟨0, 0, 0, algebraMap R₀ K a, algebraMap R₀ K b⟩ := by ext <;> simp [WeierstrassCurve.map]
  have hmapW₀ : ((⟨0, 0, 0, a₀, b₀⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)) =
      ⟨0, 0, 0, algebraMap R₀ K a₀, algebraMap R₀ K b₀⟩ := by ext <;> simp [WeierstrassCurve.map]
  rw [hmapW₁, hmapW₀]
  exact WeierstrassCurve.GoodModel.smul_short_eq_of_eq_pow_mul _ hπK0 m _ _ _ _
    (by rw [ha₀, map_mul, map_pow]) (by rw [hb₀, map_mul, map_pow])

end S_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range (solution)
