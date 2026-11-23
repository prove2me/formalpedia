-- Prove2me | solution 1 for SumProduct.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:45:10.613731+00:00
-- url     : https://prove2.me/submissions/e2bc6f9b-bee6-4526-b747-92117b48b89f

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_Martinet
import Definitions.Def_SumProduct_AdditiveCount
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_RegulatorBound
import Definitions.Def_SumProduct_Construction
import Theorems.Thm_SumProduct_lemma_4_1
section
open scoped NumberField
open Pointwise
namespace SumProduct
private lemma rpow_natpow_comm {b : ℝ} (hb : 0 ≤ b) (t : ℝ) (m : ℕ) :
    (b ^ m) ^ t = (b ^ t) ^ m := by
  rw [← Real.rpow_natCast_mul hb, mul_comm, Real.rpow_mul_natCast hb]
private lemma exists_real_embedding (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] : ∃ f : 𝓞 K →+* ℝ, Function.Injective f := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  have hw : w.IsReal := NumberField.IsTotallyReal.isReal w
  exact ⟨(NumberField.InfinitePlace.embedding_of_isReal hw).comp (algebraMap (𝓞 K) K),
    (NumberField.InfinitePlace.embedding_of_isReal hw).injective.comp
      NumberField.RingOfIntegers.coe_injective⟩
end SumProduct
end

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution (hMartinet : MartinetTotallyRealTowers) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧ 2 ≤ d ∧ ∀ X : ℝ, 1 ≤ X →
      ∃ A : Finset ℝ,
        X ^ d ≤ (A.card : ℝ) ∧ (A.card : ℝ) ≤ (C * X) ^ d ∧
        ((A + A).card : ℝ) ≤ C ^ d * (A.card : ℝ) ∧
        ((A * A).card : ℝ) ≤ (A.card : ℝ) ^ 2 / 2 ^ d := by
  classical
  obtain ⟨c₁, hc₁, L⟩ := lemma_4_1
  change ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d at hMartinet
  obtain ⟨C, hC, T⟩ := hMartinet
  -- Work with `Cd = max C 1 ≥ 1` as the discriminant base, `Y = max (4 Cd²/c₁) 2 ≥ 2` constant.
  set Cd : ℝ := max C 1 with hCddef
  have hCd1 : 1 ≤ Cd := le_max_right _ _
  have hCd0 : 0 < Cd := lt_of_lt_of_le one_pos hCd1
  have hCCd : C ≤ Cd := le_max_left _ _
  set Y : ℝ := max (4 * Cd ^ 2 / c₁) 2 with hYdef
  have hY2 : 2 ≤ Y := le_max_right _ _
  have hY0 : 0 < Y := lt_of_lt_of_le two_pos hY2
  have hYbig : 4 * Cd ^ 2 / c₁ ≤ Y := le_max_left _ _
  -- The output constant.
  set Cout : ℝ := max (3 * Y / c₁) ((Real.exp Y / c₁) * Cd ^ ((1 : ℝ) / 2)) with hCoutdef
  have hCout0 : 0 < Cout :=
    lt_of_lt_of_le (show (0 : ℝ) < 3 * Y / c₁ by positivity) (le_max_left _ _)
  refine ⟨Cout, hCout0, fun N => ?_⟩
  obtain ⟨d₀, hd₀⟩ := pow_unbounded_of_one_lt Y one_lt_two
  obtain ⟨d, hdge, K, iF, iNF, iTR, hdeg, hdiscr⟩ := T (max (max N d₀) 2)
  letI := iF; letI := iNF; letI := iTR
  have hdN : N ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hdge
  have hdd0 : d₀ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hdge
  have hd2 : 2 ≤ d := le_trans (le_max_right _ _) hdge
  have hY2d : Y < (2 : ℝ) ^ d := lt_of_lt_of_le hd₀ (pow_le_pow_right₀ one_le_two hdd0)
  refine ⟨d, hdN, hd2, fun X hX1 => ?_⟩
  set Xt : ℝ := max X 2 with hXtdef
  have hXt2 : 2 ≤ Xt := le_max_right _ _
  have hXt0 : 0 < Xt := lt_of_lt_of_le two_pos hXt2
  obtain ⟨A, hAlow, hAhigh, hAmul, hAadd⟩ := L K d hdeg hd2 Xt Y hXt2 hY2
  obtain ⟨f, hf⟩ := exists_real_embedding K
  set A' : Finset ℝ := A.image f with hA'def
  have hcard : A'.card = A.card := by rw [hA'def]; exact Finset.card_image_of_injective A hf
  have hcardadd : (A' + A').card = (A + A).card := by
    rw [hA'def, ← Finset.image_add]; exact Finset.card_image_of_injective _ hf
  have hcardmul : (A' * A').card = (A * A).card := by
    rw [hA'def, ← Finset.image_mul]; exact Finset.card_image_of_injective _ hf
  set D : ℝ := |(NumberField.discr K : ℝ)| with hDdef
  have hDpos : 0 < D := by
    rw [hDdef, abs_pos]
    exact Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hD0 : 0 ≤ D := hDpos.le
  have hDCd : D ≤ Cd ^ d := le_trans hdiscr (pow_le_pow_left₀ hC.le hCCd d)
  -- `4 Cd² ≤ c₁ Y`, the master inequality behind all the constant choices.
  have hc1Y : 4 * Cd ^ 2 ≤ c₁ * Y := by
    rw [mul_comm c₁ Y]; exact (div_le_iff₀ hc₁).mp hYbig
  refine ⟨A', ?_, ?_, ?_, ?_⟩
  · -- `X^d ≤ |A'|`
    rw [hcard]
    -- `D^{3/2} ≤ (Cd^{3/2})^d`
    have hE : D ^ ((3 : ℝ) / 2) ≤ (Cd ^ ((3 : ℝ) / 2)) ^ d := by
      rw [← rpow_natpow_comm hCd0.le]; exact Real.rpow_le_rpow hD0 hDCd (by norm_num)
    -- `Cd^{3/2} ≤ Cd²`, hence `2 Cd^{3/2} ≤ c₁ Y`.
    have hCd32 : Cd ^ ((3 : ℝ) / 2) ≤ Cd ^ 2 := by
      have h2 : (Cd : ℝ) ^ 2 = Cd ^ (2 : ℝ) := by rw [← Real.rpow_natCast Cd 2]; norm_num
      rw [h2]; exact Real.rpow_le_rpow_of_exponent_le hCd1 (by norm_num)
    have hbound : 2 * Cd ^ ((3 : ℝ) / 2) ≤ c₁ * Y := by nlinarith [sq_nonneg Cd, hCd32, hc1Y]
    -- `Y · D^{3/2} ≤ (c₁ Y)^d`
    have hYD : Y * D ^ ((3 : ℝ) / 2) ≤ (c₁ * Y) ^ d := by
      calc Y * D ^ ((3 : ℝ) / 2)
          ≤ Y * (Cd ^ ((3 : ℝ) / 2)) ^ d := by
            exact mul_le_mul_of_nonneg_left hE hY0.le
        _ ≤ (2 : ℝ) ^ d * (Cd ^ ((3 : ℝ) / 2)) ^ d :=
            mul_le_mul_of_nonneg_right hY2d.le (by positivity)
        _ = (2 * Cd ^ ((3 : ℝ) / 2)) ^ d := by rw [← mul_pow]
        _ ≤ (c₁ * Y) ^ d := pow_le_pow_left₀ (by positivity) hbound d
    have hden : 0 < Y * D ^ ((3 : ℝ) / 2) := by positivity
    -- `Xt^d ≤ |A|`, then `X^d ≤ Xt^d ≤ |A|`.
    have hXtlow : Xt ^ d ≤ (A.card : ℝ) := by
      refine le_trans ?_ hAlow
      rw [le_div_iff₀ hden, show c₁ * Xt * Y = Xt * (c₁ * Y) by ring, mul_pow]
      exact mul_le_mul_of_nonneg_left hYD (by positivity)
    exact le_trans (pow_le_pow_left₀ (by linarith) (le_max_left X 2) d) hXtlow
  · -- `|A'| ≤ (Cout X)^d`
    rw [hcard]
    have hXt3 : Xt ≤ 3 * X := by rw [hXtdef]; exact max_le (by linarith) (by linarith)
    have h3Y : 3 * Y / c₁ ≤ Cout := by rw [hCoutdef]; exact le_max_left _ _
    have hstep : Xt * Y / c₁ ≤ Cout * X := by
      calc Xt * Y / c₁ = (Y / c₁) * Xt := by ring
        _ ≤ (Y / c₁) * (3 * X) := by
            exact mul_le_mul_of_nonneg_left hXt3 (by positivity)
        _ = (3 * Y / c₁) * X := by ring
        _ ≤ Cout * X := mul_le_mul_of_nonneg_right h3Y (by linarith)
    exact le_trans hAhigh (pow_le_pow_left₀ (by positivity) hstep d)
  · -- `|A' + A'| ≤ Cout^d |A'|`
    rw [hcardadd, hcard]
    have hE2 : D ^ ((1 : ℝ) / 2) ≤ (Cd ^ ((1 : ℝ) / 2)) ^ d := by
      rw [← rpow_natpow_comm hCd0.le]; exact Real.rpow_le_rpow hD0 hDCd (by norm_num)
    have hfac : (Real.exp Y / c₁) * Cd ^ ((1 : ℝ) / 2) ≤ Cout := by
      rw [hCoutdef]; exact le_max_right _ _
    have hcombine : (Real.exp Y / c₁) ^ d * D ^ ((1 : ℝ) / 2) ≤ Cout ^ d := by
      calc (Real.exp Y / c₁) ^ d * D ^ ((1 : ℝ) / 2)
          ≤ (Real.exp Y / c₁) ^ d * (Cd ^ ((1 : ℝ) / 2)) ^ d := by
            exact mul_le_mul_of_nonneg_left hE2 (by positivity)
        _ = ((Real.exp Y / c₁) * Cd ^ ((1 : ℝ) / 2)) ^ d := by rw [← mul_pow]
        _ ≤ Cout ^ d := pow_le_pow_left₀ (by positivity) hfac d
    calc (↑(A + A).card : ℝ)
        ≤ (Real.exp Y / c₁) ^ d * D ^ ((1 : ℝ) / 2) * (A.card : ℝ) := hAadd
      _ ≤ Cout ^ d * (A.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hcombine (by positivity)
  · -- `|A' · A'| ≤ |A'|² / 2^d`
    rw [hcardmul, hcard]
    have hD2 : D ^ 2 ≤ (Cd ^ 2) ^ d := by
      calc D ^ 2 ≤ (Cd ^ d) ^ 2 := pow_le_pow_left₀ hD0 hDCd 2
        _ = (Cd ^ 2) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm]
    have hKey2 : D ^ 2 * Y * (2 : ℝ) ^ d ≤ (c₁ * Y) ^ d := by
      calc D ^ 2 * Y * (2 : ℝ) ^ d
          ≤ (Cd ^ 2) ^ d * (2 : ℝ) ^ d * (2 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hD2 hY2d.le hY0.le (by positivity)) (by positivity)
        _ = (4 * Cd ^ 2) ^ d := by rw [mul_assoc, ← mul_pow, ← mul_pow]; congr 1; ring
        _ ≤ (c₁ * Y) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    have hzc : c₁ ^ (-(d : ℤ)) = (c₁ ^ d)⁻¹ := by rw [zpow_neg, zpow_natCast]
    have hzy : Y ^ (1 - (d : ℤ)) = Y * (Y ^ d)⁻¹ := by
      rw [show (1 : ℤ) - (d : ℤ) = 1 + (-(d : ℤ)) by ring, zpow_add₀ hY0.ne', zpow_one, zpow_neg,
        zpow_natCast]
    have hcoef : c₁ ^ (-(d : ℤ)) * Y ^ (1 - (d : ℤ)) * D ^ 2 ≤ ((2 : ℝ) ^ d)⁻¹ := by
      rw [hzc, hzy,
        show (c₁ ^ d)⁻¹ * (Y * (Y ^ d)⁻¹) * D ^ 2 = D ^ 2 * Y / (c₁ ^ d * Y ^ d) by
          field_simp,
        div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity), ← mul_pow]
      exact hKey2
    calc (↑(A * A).card : ℝ)
        ≤ c₁ ^ (-(d : ℤ)) * Y ^ (1 - (d : ℤ)) * D ^ 2 * (A.card : ℝ) ^ 2 := hAmul
      _ ≤ ((2 : ℝ) ^ d)⁻¹ * (A.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = (A.card : ℝ) ^ 2 / 2 ^ d := by rw [div_eq_mul_inv, mul_comm]
end SumProduct
