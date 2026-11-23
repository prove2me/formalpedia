-- Prove2me | solution 1 for SumProduct.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:40:58.734548+00:00
-- url     : https://prove2.me/submissions/85c49f0c-826c-447a-a3d5-32d38a7eeb3a

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
import Theorems.Thm_SumProduct_card_mul_self_le
import Theorems.Thm_SumProduct_place_construction_le
import Theorems.Thm_SumProduct_card_construction_floor
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_SumProduct_boxAdd_add
import Theorems.Thm_SumProduct_boxMult_mul
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
import Theorems.Thm_SumProduct_latticeEmbed_apply
import Theorems.Thm_SumProduct_latticeEquiv_coe
import Theorems.Thm_SumProduct_lattice_count_add
import Theorems.Thm_SumProduct_lattice_count_mult
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_regulator_le_discr
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply
attribute [local simp] SumProduct.idealCountArith_apply_ne
attribute [local simp] SumProduct.latticeEmbed_apply
attribute [local simp] SumProduct.latticeEquiv_coe
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection


section
open scoped NumberField
open Pointwise
namespace SumProduct
private lemma sqrt_le_fifteen_pow {d : ℕ} : Real.sqrt (d : ℝ) ≤ 15 ^ d := by
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have h1 : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
    have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (two_ne_zero) d
    have h := Real.sqrt_le_sqrt hdd
    rwa [Real.sqrt_sq hdnn] at h
  have h2 : (d : ℝ) ≤ 15 ^ d := by
    calc (d : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
      _ ≤ 15 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  linarith
private lemma aux_L1 {X Y D : ℝ} (hX : 2 ≤ X) (hY : 2 ≤ Y) {d : ℕ} (hd : 1 ≤ d) (hD : 1 ≤ D) :
    ((1 : ℝ) / 100 * X * Y) ^ d / (Y * D ^ ((3 : ℝ) / 2))
      ≤ Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D) * (((3 : ℝ) / 20 * X) ^ d / Real.sqrt D) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hsD : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hDsD : D * Real.sqrt D = D ^ ((3 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hD0, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  -- reduced inequality (denominators `D^{3/2}=D√D` cancel)
  have hred : ((1 : ℝ) / 100 * X * Y) ^ d / Y
      ≤ Y ^ (d - 1) * ((3 : ℝ) / 20 * X) ^ d / Real.sqrt (d : ℝ) := by
    rw [div_le_div_iff₀ hY0 hsd]
    have hrhs : Y ^ (d - 1) * ((3 : ℝ) / 20 * X) ^ d * Y
        = 15 ^ d * ((1 : ℝ) / 100 * X * Y) ^ d := by
      rw [show Y ^ (d - 1) * ((3 : ℝ) / 20 * X) ^ d * Y
          = (Y ^ (d - 1) * Y) * ((3 : ℝ) / 20 * X) ^ d by ring, ← pow_succ, Nat.sub_add_cancel hd,
        ← mul_pow, ← mul_pow]
      congr 1
      ring
    rw [hrhs]
    nlinarith [sqrt_le_fifteen_pow (d := d), pow_pos (show (0:ℝ) < 1/100*X*Y by positivity) d]
  calc ((1 : ℝ) / 100 * X * Y) ^ d / (Y * D ^ ((3 : ℝ) / 2))
      = (((1 : ℝ) / 100 * X * Y) ^ d / Y) / (D * Real.sqrt D) := by rw [hDsD]; ring
    _ ≤ (Y ^ (d - 1) * ((3 : ℝ) / 20 * X) ^ d / Real.sqrt (d : ℝ)) / (D * Real.sqrt D) :=
        (div_le_div_iff_of_pos_right (mul_pos hD0 hsD)).mpr hred
    _ = Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D) * (((3 : ℝ) / 20 * X) ^ d / Real.sqrt D) := by
        rw [div_mul_div_comm, div_div, mul_assoc]
private lemma aux_L2 {X Y : ℝ} (hX : 2 ≤ X) (hY : 2 ≤ Y) {d : ℕ} (hd : 2 ≤ d) :
    10 * (5 * Y + 1) ^ (d - 1) * (2 * ((3 : ℝ) / 20 * X) + 1) ^ d
      ≤ (X * Y / (1 / 100)) ^ d := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hd1 : 1 ≤ d := by omega
  have h1 : (5 * Y + 1) ^ (d - 1) ≤ (6 * Y) ^ d :=
    calc (5 * Y + 1) ^ (d - 1) ≤ (6 * Y) ^ (d - 1) := by gcongr; linarith
      _ ≤ (6 * Y) ^ d := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : (2 * ((3 : ℝ) / 20 * X) + 1) ^ d ≤ X ^ d := by
    apply pow_le_pow_left₀ (by positivity); nlinarith
  have hpow : (10 : ℝ) * 6 ^ d ≤ 100 ^ d := by
    have h10 : (10 : ℝ) ≤ (100 / 6) ^ d :=
      le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num) hd)
    have h100 : (100 : ℝ) ^ d = (100 / 6) ^ d * 6 ^ d := by rw [← mul_pow]; norm_num
    nlinarith [h10, pow_pos (show (0 : ℝ) < 6 by norm_num) d]
  have hXYpos : (0 : ℝ) ≤ (X * Y) ^ d := by positivity
  calc 10 * (5 * Y + 1) ^ (d - 1) * (2 * ((3 : ℝ) / 20 * X) + 1) ^ d
      ≤ 10 * (6 * Y) ^ d * X ^ d := by gcongr
    _ = 10 * 6 ^ d * (X * Y) ^ d := by rw [mul_pow, mul_pow]; ring
    _ ≤ 100 ^ d * (X * Y) ^ d := by nlinarith [hpow, hXYpos]
    _ = (X * Y / (1 / 100)) ^ d := by rw [← mul_pow]; ring_nf
private lemma aux_L3 {Y : ℝ} (hY : 2 ≤ Y) {d : ℕ} (hd : 2 ≤ d) :
    10 * (d : ℝ) * (10 * Y + 1) ^ (d - 1) ≤ 100 ^ d * Y ^ (d - 1) := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hd2d : (d : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
  have hcore : (10 : ℝ) * 2 ^ d * 11 ^ (d - 1) ≤ 100 ^ d := by
    have h22 : (22 : ℝ) ^ d = 2 ^ d * 11 ^ d := by rw [← mul_pow]; norm_num
    have h11 : (11 : ℝ) ^ d = 11 * 11 ^ (d - 1) := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    have e : (10 : ℝ) * 2 ^ d * 11 ^ (d - 1) = 10 / 11 * 22 ^ d := by rw [h22, h11]; ring
    rw [e]
    calc (10 : ℝ) / 11 * 22 ^ d ≤ 1 * 22 ^ d := by gcongr; norm_num
      _ = 22 ^ d := one_mul _
      _ ≤ 100 ^ d := by gcongr; norm_num
  calc 10 * (d : ℝ) * (10 * Y + 1) ^ (d - 1)
      ≤ 10 * 2 ^ d * (11 * Y) ^ (d - 1) := by gcongr; first | exact hd2d | linarith
    _ = 10 * 2 ^ d * 11 ^ (d - 1) * Y ^ (d - 1) := by rw [mul_pow]; ring
    _ ≤ 100 ^ d * Y ^ (d - 1) := by gcongr
private lemma aux_L4 {X Y : ℝ} (hX : 2 ≤ X) (hY : 0 ≤ Y) :
    8 * X * Real.exp Y + 1 ≤ Real.exp Y * ((3 : ℝ) / 20 * X) / (1 / 100) := by
  have he : (1 : ℝ) ≤ Real.exp Y := Real.one_le_exp hY
  have hXe : (1 : ℝ) ≤ X * Real.exp Y := by nlinarith
  rw [show Real.exp Y * ((3 : ℝ) / 20 * X) / (1 / 100) = 15 * X * Real.exp Y by ring]
  nlinarith [hXe]
end SumProduct
end

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open Real
namespace SumProduct
theorem _root_.solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
      (d : ℕ), Module.finrank ℚ K = d → 2 ≤ d → ∀ X Y : ℝ, 2 ≤ X → 2 ≤ Y →
      ∃ A : Finset (𝓞 K),
        (c * X * Y) ^ d / (Y * |(NumberField.discr K : ℝ)| ^ ((3 : ℝ) / 2)) ≤ (A.card : ℝ) ∧
        (A.card : ℝ) ≤ (X * Y / c) ^ d ∧
        ((A * A).card : ℝ) ≤
          c ^ (-(d : ℤ)) * Y ^ (1 - (d : ℤ)) * |(NumberField.discr K : ℝ)| ^ 2 * (A.card : ℝ) ^ 2 ∧
        ((A + A).card : ℝ) ≤
          (Real.exp Y / c) ^ d * |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2) * (A.card : ℝ) := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro K _ _ _ d hd hd2 X Y hX hY
  classical
  have hd1 : 1 ≤ d := by omega
  set D : ℝ := |(NumberField.discr K : ℝ)| with hDdef
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hDdef, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  have hD0 : (0 : ℝ) < D := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hsqrtd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hsqrtD : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hRpos : (0 : ℝ) < NumberField.Units.regulator K := NumberField.Units.regulator_pos K
  have hReg : NumberField.Units.regulator K ≤ D := by
    rw [hDdef]; exact regulator_le_discr K (by rw [hd]; exact hd2)
  obtain ⟨hGlo, hGhi⟩ := lattice_count_mult K d hd Y hY1
  obtain ⟨_, hGGhi⟩ := lattice_count_mult K d hd (2 * Y) (by linarith)
  obtain ⟨hBlo, hBhi⟩ := lattice_count_add K d hd (3 / 20 * X) (by positivity)
  set n : ℕ := ⌊X⌋₊ with hndef
  set Gc : Finset (𝓞 K) := (boxMult K Y).image (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) with hGcdef
  set P : Finset (𝓞 K) := (boxAdd K (3 / 20 * X)).image (fun b => (n : 𝓞 K) + b) with hPdef
  have hPcard : P.card = (boxAdd K (3 / 20 * X)).card :=
    Finset.card_image_of_injective _ (add_right_injective _)
  have hGcard1 : (1 : ℝ) ≤ ((boxMult K Y).card : ℝ) := by
    have h1 : (1 : (𝓞 K)ˣ) ∈ boxMult K Y := by
      rw [mem_boxMult]; intro w
      simp only [Units.val_one, map_one, Real.log_one, abs_zero]; linarith
    exact_mod_cast Finset.card_pos.mpr ⟨1, h1⟩
  have hAeq : Gc * P = (boxMult K Y ×ˢ boxAdd K (3 / 20 * X)).image
      (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((n : 𝓞 K) + gb.2)) := by
    rw [hGcdef, hPdef]; ext x
    constructor
    · intro hx
      obtain ⟨a, ha, e, he, rfl⟩ := Finset.mem_mul.mp hx
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨(g, w), Finset.mem_product.mpr ⟨hg, hw⟩, rfl⟩
    · intro hx
      obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mul_mem_mul
        (Finset.mem_image_of_mem (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) (Finset.mem_product.mp hpr).1)
        (Finset.mem_image_of_mem (fun b => (n : 𝓞 K) + b) (Finset.mem_product.mp hpr).2)
  have hAcard : (Gc * P).card = (boxMult K Y).card * (boxAdd K (3 / 20 * X)).card := by
    rw [hAeq]; exact card_construction_floor K Y hX (by norm_num) (le_refl _)
  have hGlo' : Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D) ≤ ((boxMult K Y).card : ℝ) := by
    refine le_trans ?_ hGlo; gcongr
  refine ⟨Gc * P, ?_, ?_, ?_, ?_⟩
  · rw [hAcard]; push_cast
    refine le_trans (aux_L1 hX hY hd1 hD1) ?_
    exact mul_le_mul hGlo' hBlo (by positivity) (Nat.cast_nonneg _)
  · rw [hAcard]; push_cast
    refine le_trans ?_ (aux_L2 hX hY hd2)
    exact mul_le_mul hGhi hBhi (Nat.cast_nonneg _) (by positivity)
  · have hGGsub : Gc * Gc ⊆ (boxMult K (2 * Y)).image (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) := by
      intro z hz
      rw [hGcdef] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hz
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hb
      have hggmem : g * g' ∈ boxMult K (2 * Y) := by
        have := boxMult_mul hg hg'; rwa [show Y + Y = 2 * Y by ring] at this
      rw [show (g : 𝓞 K) * (g' : 𝓞 K) = ((g * g' : (𝓞 K)ˣ) : 𝓞 K) from (Units.val_mul g g').symm]
      exact Finset.mem_image_of_mem (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) hggmem
    have hAA : (((Gc * P) * (Gc * P)).card : ℝ)
        ≤ 10 * (10 * Y + 1) ^ (d - 1) * ((boxAdd K (3 / 20 * X)).card : ℝ) ^ 2 := by
      have h1 := card_mul_self_le Gc P
      have h2 : (Gc * Gc).card ≤ (boxMult K (2 * Y)).card :=
        le_trans (Finset.card_le_card hGGsub) Finset.card_image_le
      have h3 : (P * P).card ≤ (boxAdd K (3 / 20 * X)).card ^ 2 := by
        calc (P * P).card ≤ P.card * P.card := Finset.card_mul_le
          _ = (boxAdd K (3 / 20 * X)).card ^ 2 := by rw [hPcard]; ring
      have hGG : ((Gc * Gc).card : ℝ) ≤ 10 * (10 * Y + 1) ^ (d - 1) := by
        have h2' : ((Gc * Gc).card : ℝ) ≤ ((boxMult K (2 * Y)).card : ℝ) := by exact_mod_cast h2
        refine le_trans h2' ?_
        rw [show (10 : ℝ) * Y + 1 = 5 * (2 * Y) + 1 by ring]; exact hGGhi
      calc (((Gc * P) * (Gc * P)).card : ℝ)
          ≤ ((Gc * Gc).card : ℝ) * ((P * P).card : ℝ) := by exact_mod_cast h1
        _ ≤ 10 * (10 * Y + 1) ^ (d - 1) * ((boxAdd K (3 / 20 * X)).card : ℝ) ^ 2 := by
            gcongr; exact_mod_cast h3
    refine le_trans hAA ?_
    rw [hAcard]; push_cast
    rw [show ((1 : ℝ) / 100) ^ (-(d : ℤ)) = 100 ^ d by
          rw [zpow_neg, zpow_natCast, one_div, inv_pow, inv_inv],
       show Y ^ (1 - (d : ℤ)) = Y * (Y ^ d)⁻¹ by
          rw [show (1 : ℤ) - (d : ℤ) = 1 + (-(d : ℤ)) by ring, zpow_add₀ hY0.ne', zpow_one,
            zpow_neg, zpow_natCast]]
    have hYpow : (Y : ℝ) ^ d = Y ^ (d - 1) * Y := by rw [← pow_succ, Nat.sub_add_cancel hd1]
    have heq : (100 : ℝ) ^ d * (Y * (Y ^ d)⁻¹) * D ^ 2 *
        (Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D)) ^ 2 = 100 ^ d * Y ^ (d - 1) / (d : ℝ) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hdpos.le, hYpow]
      field_simp
    have hcardsq : (Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D)) ^ 2 ≤ ((boxMult K Y).card : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hGlo' 2
    have hcoeff : 10 * (10 * Y + 1) ^ (d - 1)
        ≤ 100 ^ d * (Y * (Y ^ d)⁻¹) * D ^ 2 * ((boxMult K Y).card : ℝ) ^ 2 := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hcardsq (by positivity))
      rw [heq, le_div_iff₀ hdpos]
      nlinarith [aux_L3 hY hd2]
    rw [mul_pow,
      show (100 : ℝ) ^ d * (Y * (Y ^ d)⁻¹) * D ^ 2 *
          (((boxMult K Y).card : ℝ) ^ 2 * ((boxAdd K (3 / 20 * X)).card : ℝ) ^ 2)
        = (100 ^ d * (Y * (Y ^ d)⁻¹) * D ^ 2 * ((boxMult K Y).card : ℝ) ^ 2) *
          ((boxAdd K (3 / 20 * X)).card : ℝ) ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
  · have hAAsub : (Gc * P) + (Gc * P) ⊆ boxAdd K (4 * X * Real.exp Y) := by
      have hnX : (n : ℝ) ≤ X := Nat.floor_le hX0.le
      have hsub : ∀ z ∈ Gc * P, z ∈ boxAdd K (Real.exp Y * ((n : ℝ) + 3 / 20 * X)) := by
        intro z hz
        rw [hGcdef, hPdef] at hz
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hz
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
        rw [mem_boxAdd]; intro w; exact place_construction_le w hg hc
      intro x hx
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Finset.mem_add.mp hx
      have h12 := boxAdd_add (hsub a₁ ha₁) (hsub a₂ ha₂)
      rw [mem_boxAdd] at h12 ⊢
      intro w
      refine le_trans (h12 w) ?_
      have he : (0 : ℝ) < Real.exp Y := Real.exp_pos Y
      nlinarith [hnX, he, hX0, mul_le_mul_of_nonneg_left hnX he.le]
    have hcard : (((Gc * P) + (Gc * P)).card : ℝ) ≤ (2 * (4 * X * Real.exp Y) + 1) ^ d :=
      le_trans (by exact_mod_cast Finset.card_le_card hAAsub)
        (lattice_count_add K d hd (4 * X * Real.exp Y) (by positivity)).2
    refine le_trans hcard ?_
    rw [hAcard, show D ^ ((1 : ℝ) / 2) = Real.sqrt D from (Real.sqrt_eq_rpow D).symm]
    push_cast
    have hcardGB : (3 / 20 * X) ^ d / Real.sqrt D
        ≤ ((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ) := by
      calc (3 / 20 * X) ^ d / Real.sqrt D ≤ ((boxAdd K (3 / 20 * X)).card : ℝ) := hBlo
        _ = 1 * ((boxAdd K (3 / 20 * X)).card : ℝ) := (one_mul _).symm
        _ ≤ ((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ) := by
            gcongr
    have hDcardA : (3 / 20 * X) ^ d
        ≤ Real.sqrt D * (((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ)) := by
      rw [mul_comm (Real.sqrt D)]; exact (div_le_iff₀ hsqrtD).mp hcardGB
    calc (2 * (4 * X * Real.exp Y) + 1) ^ d
        ≤ (Real.exp Y * ((3 : ℝ) / 20 * X) / (1 / 100)) ^ d := by
          apply pow_le_pow_left₀ (by positivity)
          have := aux_L4 hX hY0.le; linarith [this]
      _ = (Real.exp Y / (1 / 100)) ^ d * (3 / 20 * X) ^ d := by
          rw [← mul_pow, show Real.exp Y / (1 / 100) * (3 / 20 * X)
            = Real.exp Y * ((3 : ℝ) / 20 * X) / (1 / 100) by ring]
      _ ≤ (Real.exp Y / (1 / 100)) ^ d *
            (Real.sqrt D * (((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ))) := by
          gcongr
      _ = (Real.exp Y / (1 / 100)) ^ d * Real.sqrt D *
            (((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ)) := by ring
end SumProduct
