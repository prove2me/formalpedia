-- Prove2me | solution 1 for RatIdele.exists_norm_apply_eq_ideleNorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/78090323-089c-5509-916a-5624d7257e5c

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain NumberField.AdelicLevel RatIdele

namespace ModuleOfIdeleClassCharacter

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

private def integralSubmonoid : Submonoid 𝔸ℚf where
  carrier := integralFiniteAdeles (𝓞 ℚ) ℚ
  one_mem' := one_mem_integralFiniteAdeles
  mul_mem' := mul_mem_integralFiniteAdeles

private def unitWindow : Subgroup (𝔸ℚf)ˣ := integralSubmonoid.units

private theorem mem_unitWindow_iff (x : (𝔸ℚf)ˣ) :
    x ∈ unitWindow ↔ (x : 𝔸ℚf) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ ∧
      ((x⁻¹ : (𝔸ℚf)ˣ) : 𝔸ℚf) ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
  Submonoid.mem_units_iff _ _

private theorem isCompact_unitWindow : IsCompact (unitWindow : Set (𝔸ℚf)ˣ) :=
  Submonoid.units_isCompact (isCompact_integralFiniteAdeles (𝓞 ℚ) ℚ)

private scoped instance : CompactSpace unitWindow := isCompact_iff_compactSpace.mp isCompact_unitWindow

private scoped instance : TotallyDisconnectedSpace 𝔸ℚf :=
  ⟨isTotallyDisconnected_of_image
    (f := ((⇑) : 𝔸ℚf → ∀ w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletion ℚ))
    RestrictedProduct.continuous_coe.continuousOn DFunLike.coe_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private scoped instance : TotallyDisconnectedSpace (𝔸ℚf)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.totallyDisconnectedSpace

private scoped instance : TotallyDisconnectedSpace (𝔸ℚf)ˣ :=
  Units.isEmbedding_embedProduct.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

private theorem continuous_finIncl : Continuous (finIncl (𝓞 ℚ) ℚ : 𝔸ℚf → 𝔸ℚ) :=
  continuous_const.prodMk continuous_id

private def windowToIdele : unitWindow →* (𝔸ℚ)ˣ :=
  (Units.map (finIncl (𝓞 ℚ) ℚ)).comp unitWindow.subtype

private theorem continuous_windowToIdele : Continuous windowToIdele :=
  (continuous_finIncl.units_map (finIncl (𝓞 ℚ) ℚ)).comp continuous_subtype_val

private theorem windowToIdele_fst (u : unitWindow) : ((windowToIdele u : (𝔸ℚ)ˣ) : 𝔸ℚ).1 = 1 := rfl

private theorem windowToIdele_snd (u : unitWindow) :
    ((windowToIdele u : (𝔸ℚ)ˣ) : 𝔸ℚ).2 = ((u : (𝔸ℚf)ˣ) : 𝔸ℚf) := rfl

private def eR : Rat.infinitePlace.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

private theorem norm_eR_symm (r : ℝ) : ‖eR.symm r‖ = |r| := by
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
    Rat.isReal_infinitePlace).symm.isometry.norm_map_of_map_zero (map_zero eR.symm) r

private theorem continuous_eR_symm : Continuous eR.symm :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous

private def archUnit : ℝˣ →* (𝔸ℚ)ˣ :=
  (NumberField.TateGlobal.archUnitHom Rat.infinitePlace).comp (Units.map eR.symm.toRingHom.toMonoidHom)

private theorem archUnit_apply (r : ℝˣ) :
    archUnit r = NumberField.AdelicVolume.archCentralUnit ℚ Rat.infinitePlace
      (Units.map eR.symm.toRingHom.toMonoidHom r) := rfl

private theorem coe_archUnit_fst (r : ℝˣ) :
    ((archUnit r : (𝔸ℚ)ˣ) : 𝔸ℚ).1 Rat.infinitePlace = eR.symm (r : ℝ) := by
  rw [archUnit_apply]
  exact NumberField.AdelicVolume.archCentralUnit_fst_self Rat.infinitePlace _

private theorem coe_archUnit_snd (r : ℝˣ) : ((archUnit r : (𝔸ℚ)ˣ) : 𝔸ℚ).2 = 1 := by
  rw [archUnit_apply]
  exact NumberField.AdelicVolume.archCentralUnit_snd Rat.infinitePlace _

open scoped Classical in

private theorem coe_archCentralUnit_eq (b : (Rat.infinitePlace.Completion)ˣ) :
    ((NumberField.AdelicVolume.archCentralUnit ℚ Rat.infinitePlace b : (𝔸ℚ)ˣ) : 𝔸ℚ)
      = (Function.update (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace (b : Rat.infinitePlace.Completion),
          (1 : 𝔸ℚf)) := by
  refine Prod.ext (funext fun w => ?_) (NumberField.AdelicVolume.archCentralUnit_snd _ _)
  show ((NumberField.AdelicVolume.archCentralUnit ℚ Rat.infinitePlace b : (𝔸ℚ)ˣ) : 𝔸ℚ).1 w
    = Function.update (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace (b : Rat.infinitePlace.Completion) w
  by_cases hw : w = Rat.infinitePlace
  · subst hw
    rw [Function.update_self]
    exact NumberField.AdelicVolume.archCentralUnit_fst_self _ _
  · rw [Function.update_of_ne hw]
    exact NumberField.AdelicVolume.archCentralUnit_fst_of_ne _ _ hw

open scoped Classical in
private theorem continuous_archUnitHom :
    Continuous (NumberField.TateGlobal.archUnitHom (F := ℚ) Rat.infinitePlace) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : Continuous fun a : (Rat.infinitePlace.Completion)ˣ =>
        (Function.update (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace (a : Rat.infinitePlace.Completion), (1 : 𝔸ℚf)) :=
      (continuous_const.update Rat.infinitePlace Units.continuous_val).prodMk continuous_const
    refine h.congr fun a => ?_
    rw [Function.comp_apply, NumberField.TateGlobal.archUnitHom_apply, coe_archCentralUnit_eq]
  · have h : Continuous fun a : (Rat.infinitePlace.Completion)ˣ =>
        (Function.update (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace
          ((a⁻¹ : (Rat.infinitePlace.Completion)ˣ) : Rat.infinitePlace.Completion), (1 : 𝔸ℚf)) :=
      (continuous_const.update Rat.infinitePlace Units.continuous_coe_inv).prodMk continuous_const
    refine h.congr fun a => ?_
    rw [← map_inv (NumberField.TateGlobal.archUnitHom (F := ℚ) Rat.infinitePlace) a,
      NumberField.TateGlobal.archUnitHom_apply, coe_archCentralUnit_eq]

private theorem continuous_archUnit : Continuous archUnit :=
  continuous_archUnitHom.comp (continuous_eR_symm.units_map eR.symm.toRingHom.toMonoidHom)

private theorem ideleNorm_archUnit (r : ℝˣ) : NumberField.TateGlobal.ideleNorm ℚ (archUnit r) = |(r : ℝ)| := by
  show ((MeasureTheory.distribHaarChar 𝔸ℚ (archUnit r) : NNReal) : ℝ) = _
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one ℚ (archUnit r) (coe_archUnit_snd r),
    Fintype.prod_unique]
  have hm : (Rat.infinitePlace).mult = 1 := InfinitePlace.mult_isReal ⟨_, Rat.isReal_infinitePlace⟩
  show ‖((archUnit r : (𝔸ℚ)ˣ) : 𝔸ℚ).1 Rat.infinitePlace‖ ^ (Rat.infinitePlace).mult = |(r : ℝ)|
  rw [hm, pow_one, coe_archUnit_fst]
  exact norm_eR_symm r

private def expUnit (s : ℝ) : ℝˣ := Units.mk0 (Real.exp s) (Real.exp_ne_zero s)

private theorem coe_expUnit (s : ℝ) : ((expUnit s : ℝˣ) : ℝ) = Real.exp s := rfl

private theorem expUnit_zero : expUnit 0 = 1 := Units.ext (by rw [coe_expUnit, Real.exp_zero, Units.val_one])

private theorem expUnit_add (s s' : ℝ) : expUnit (s + s') = expUnit s * expUnit s' :=
  Units.ext (by rw [Units.val_mul, coe_expUnit, coe_expUnit, coe_expUnit, Real.exp_add])

private theorem continuous_expUnit : Continuous expUnit := by
  refine Units.continuous_iff.2 ⟨Real.continuous_exp, ?_⟩
  simp only [expUnit, Units.val_inv_eq_inv_val, Units.val_mk0]
  exact Real.continuous_exp.inv₀ fun s => Real.exp_ne_zero s

private theorem eq_expUnit_log (r : ℝˣ) (hr : 0 < (r : ℝ)) : r = expUnit (Real.log r) :=
  Units.ext (by rw [coe_expUnit, Real.exp_log hr])

private theorem ideleNorm_principal (q : ℚˣ) :
    NumberField.TateGlobal.ideleNorm ℚ (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = 1 := by
  letI : MeasurableSpace 𝔸ℚ := borel 𝔸ℚ
  haveI : BorelSpace 𝔸ℚ := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ q
  show ((MeasureTheory.distribHaarChar 𝔸ℚ (Units.map (algebraMap ℚ 𝔸ℚ).toMonoidHom q) : NNReal) : ℝ) = 1
  rw [h, NNReal.coe_one]

private theorem exists_eq_mul (x : (𝔸ℚ)ˣ) :
    ∃ (q : ℚˣ) (a : ℝˣ) (u : unitWindow), 0 < (a : ℝ) ∧
      x = Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q * (archUnit a * windowToIdele u) := by
  set q : ℚˣ := Units.mk0 (ρ x) (ρ_ne_zero x) with hq
  set P : (𝔸ℚ)ˣ := Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q with hP
  set x' : (𝔸ℚ)ˣ := P⁻¹ * x with hx'

  have hPv : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((P : 𝔸ℚ).2 v) = v.valuation ℚ (ρ x) := fun v => by
    rw [hP, Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd, valued_algebraMap_rat, hq, Units.val_mk0]
  have hval : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((x' : 𝔸ℚ).2 v) = 1 := fun v => by
    have h := valued_snd_inv_mul P v
    rw [hPv v] at h
    rw [hx', valued_snd_mul, (ρ_spec x).1 v]
    exact h
  have hval' : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (((x'⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v) = 1 := fun v => by
    have h := valued_snd_inv_mul x' v
    rwa [hval v, mul_one] at h
  have hmem : finPart x' ∈ unitWindow := by
    refine (mem_unitWindow_iff _).2 ⟨fun v => ?_, fun v => ?_⟩
    · exact (hval v).le
    · rw [← map_inv]
      exact (hval' v).le

  have harchP : archCoord P = ((ρ x : ℚ) : ℝ) := by
    rw [hP, archCoord_principal, hq, Units.val_mk0]
  have harchPinv : archCoord (P⁻¹ : (𝔸ℚ)ˣ) = (((ρ x : ℚ) : ℝ))⁻¹ := by
    have h := archCoord_mul P P⁻¹
    rw [mul_inv_cancel, archCoord_one, harchP] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hρ : ((ρ x : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ρ_ne_zero x
  have hpos : 0 < archCoord x' := by
    have h := (ρ_spec x).2
    rw [hx', archCoord_mul, harchPinv, inv_mul_eq_div, ← mul_div_mul_right (archCoord x) _ hρ]
    exact div_pos h (mul_self_pos.2 hρ)
  set a : ℝˣ := Units.mk0 (archCoord x') (archCoord_ne_zero x') with ha
  have hapos : 0 < (a : ℝ) := hpos

  have hdecomp : x' = archUnit a * windowToIdele ⟨finPart x', hmem⟩ := by
    refine Units.ext (Prod.ext ?_ ?_)
    · show (x' : 𝔸ℚ).1 = ((archUnit a : (𝔸ℚ)ˣ) : 𝔸ℚ).1 * ((windowToIdele ⟨finPart x', hmem⟩ : (𝔸ℚ)ˣ) : 𝔸ℚ).1
      rw [windowToIdele_fst, mul_one]
      funext w
      obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      rw [coe_archUnit_fst]
      show (x' : 𝔸ℚ).1 Rat.infinitePlace = eR.symm (eR ((x' : 𝔸ℚ).1 Rat.infinitePlace))
      exact (eR.symm_apply_apply _).symm
    · show (x' : 𝔸ℚ).2 = ((archUnit a : (𝔸ℚ)ˣ) : 𝔸ℚ).2 * ((windowToIdele ⟨finPart x', hmem⟩ : (𝔸ℚ)ˣ) : 𝔸ℚ).2
      show (x' : 𝔸ℚ).2 = (1 : 𝔸ℚf) * ((finPart x' : (𝔸ℚf)ˣ) : 𝔸ℚf)
      exact (one_mul _).symm
  refine ⟨q, a, ⟨finPart x', hmem⟩, hapos, ?_⟩
  rw [← hdecomp, hx', ← hP, mul_inv_cancel_left]

private theorem apply_windowToIdele_eq_one (m : (𝔸ℚ)ˣ →* ℝ) (hpos : ∀ x, 0 < m x) (hm : Continuous m)
    (u : unitWindow) : m (windowToIdele u) = 1 := by
  obtain ⟨B, hB⟩ := (isCompact_range (hm.comp continuous_windowToIdele)).bddAbove
  have hle : ∀ w : unitWindow, m (windowToIdele w) ≤ B := fun w => hB ⟨w, rfl⟩
  have key : ∀ w : unitWindow, m (windowToIdele w) ≤ 1 := fun w => by
    by_contra hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (not_le.1 hgt)
    have h := hle (w ^ n)
    rw [map_pow, map_pow] at h
    exact lt_irrefl B (lt_of_lt_of_le hn h)
  have h₁ := key u
  have h₂ := key u⁻¹
  rw [map_inv, map_inv] at h₂
  exact le_antisymm h₁ ((inv_le_one₀ (hpos _)).1 h₂)

private def rayLog (m : (𝔸ℚ)ˣ →* ℝ) (hpos : ∀ x, 0 < m x) : ℝ →+ ℝ where
  toFun s := Real.log (m (archUnit (expUnit s)))
  map_zero' := by
    show Real.log (m (archUnit (expUnit 0))) = 0
    rw [expUnit_zero, map_one, map_one, Real.log_one]
  map_add' s s' := by
    show Real.log (m (archUnit (expUnit (s + s'))))
      = Real.log (m (archUnit (expUnit s))) + Real.log (m (archUnit (expUnit s')))
    rw [expUnit_add, map_mul, map_mul]
    exact Real.log_mul (hpos _).ne' (hpos _).ne'

private theorem rayLog_apply (m : (𝔸ℚ)ˣ →* ℝ) (hpos : ∀ x, 0 < m x) (s : ℝ) :
    rayLog m hpos s = Real.log (m (archUnit (expUnit s))) := rfl

private theorem continuous_rayLog (m : (𝔸ℚ)ˣ →* ℝ) (hpos : ∀ x, 0 < m x) (hm : Continuous m) :
    Continuous (rayLog m hpos) := by
  show Continuous fun s : ℝ => Real.log (m (archUnit (expUnit s)))
  exact (hm.comp (continuous_archUnit.comp continuous_expUnit)).log fun s => (hpos _).ne'

private theorem apply_archUnit_eq_rpow (m : (𝔸ℚ)ˣ →* ℝ) (hpos : ∀ x, 0 < m x) (hm : Continuous m) (r : ℝˣ)
    (hr : 0 < (r : ℝ)) : m (archUnit r) = (r : ℝ) ^ rayLog m hpos 1 := by
  have hlin : ∀ s : ℝ, rayLog m hpos s = s * rayLog m hpos 1 := fun s => by
    have h := map_real_smul (rayLog m hpos) (continuous_rayLog m hpos hm) s 1
    rwa [smul_eq_mul, smul_eq_mul, mul_one] at h
  rw [Real.rpow_def_of_pos hr, ← hlin, rayLog_apply, ← eq_expUnit_log r hr, Real.exp_log (hpos _)]

private def modulus (μ : (𝔸ℚ)ˣ →* ℂˣ) : (𝔸ℚ)ˣ →* ℝ :=
  (normHom : ℂ →*₀ ℝ).toMonoidHom.comp ((Units.coeHom ℂ).comp μ)

private theorem modulus_apply (μ : (𝔸ℚ)ˣ →* ℂˣ) (x : (𝔸ℚ)ˣ) : modulus μ x = ‖((μ x : ℂˣ) : ℂ)‖ := rfl

private theorem modulus_pos (μ : (𝔸ℚ)ˣ →* ℂˣ) (x : (𝔸ℚ)ˣ) : 0 < modulus μ x := by
  rw [modulus_apply]
  exact norm_pos_iff.2 (Units.ne_zero (μ x))

private theorem continuous_modulus (μ : (𝔸ℚ)ˣ →* ℂˣ) (hc : Continuous μ) : Continuous (modulus μ) := by
  show Continuous fun x : (𝔸ℚ)ˣ => ‖((μ x : ℂˣ) : ℂ)‖
  exact continuous_norm.comp (Units.continuous_val.comp hc)

private theorem modulus_principal (μ : (𝔸ℚ)ˣ →* ℂˣ) (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 ℚ) ℚ μ)
    (q : ℚˣ) : modulus μ (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = 1 := by
  rw [modulus_apply, hμ q, Units.val_one, norm_one]

private def ideleNormHom : (𝔸ℚ)ˣ →* ℝ where
  toFun := NumberField.TateGlobal.ideleNorm ℚ
  map_one' := by
    have h : NumberField.TateGlobal.ideleNorm ℚ (1 : (𝔸ℚ)ˣ) * NumberField.TateGlobal.ideleNorm ℚ 1
        = NumberField.TateGlobal.ideleNorm ℚ (1 : (𝔸ℚ)ˣ) * 1 := by
      rw [mul_one, ← NumberField.TateGlobal.ideleNorm_mul, one_mul]
    exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos _).ne' h
  map_mul' x y := NumberField.TateGlobal.ideleNorm_mul x y

private theorem ideleNormHom_apply (x : (𝔸ℚ)ˣ) : ideleNormHom x = NumberField.TateGlobal.ideleNorm ℚ x := rfl

private theorem ideleNormHom_pos (x : (𝔸ℚ)ˣ) : 0 < ideleNormHom x := NumberField.TateGlobal.ideleNorm_pos x

private theorem continuous_ideleNormHom : Continuous ideleNormHom := by
  show Continuous (NumberField.TateGlobal.ideleNorm ℚ)
  exact NumberField.TateGlobal.continuous_ideleNorm ℚ

private theorem ideleNormHom_principal (q : ℚˣ) : ideleNormHom (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = 1 :=
  ideleNorm_principal q

private theorem ideleNormHom_archUnit (r : ℝˣ) : ideleNormHom (archUnit r) = |(r : ℝ)| := ideleNorm_archUnit r

end ModuleOfIdeleClassCharacter
p2m_reactivate "P2MW.S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.ModuleOfIdeleClassCharacter"

open ModuleOfIdeleClassCharacter in

theorem solution
    (μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 ℚ) ℚ μ) (hc : Continuous μ) :
    ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((μ x : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm ℚ x ^ σ := by
  have hpos : ∀ x, 0 < modulus μ x := modulus_pos μ
  have hmc : Continuous (modulus μ) := continuous_modulus μ hc
  refine ⟨rayLog (modulus μ) hpos 1, fun x => ?_⟩
  obtain ⟨q, a, u, ha, rfl⟩ := exists_eq_mul x
  rw [← modulus_apply, ← ideleNormHom_apply, map_mul, map_mul, map_mul, map_mul, modulus_principal μ hμ q,
    ideleNormHom_principal q, one_mul, one_mul, apply_windowToIdele_eq_one (modulus μ) hpos hmc u,
    apply_windowToIdele_eq_one ideleNormHom ideleNormHom_pos continuous_ideleNormHom u, mul_one, mul_one,
    apply_archUnit_eq_rpow (modulus μ) hpos hmc a ha, ideleNormHom_archUnit a, abs_of_pos ha]

end
p2m_reactivate "P2MW.S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.ModuleOfIdeleClassCharacter"

end S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow
end P2MW
export P2MW.S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow (solution)
