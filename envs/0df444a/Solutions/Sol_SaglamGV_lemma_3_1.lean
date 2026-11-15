-- Prove2me | solution 1 for SaglamGV.lemma_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-14T11:39:31.223971+00:00
-- url     : https://prove2.me/submissions/cf33469d-9ac7-4f9e-b7b6-703bc2a531aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SaglamGV_muHat_third_moment_ks
import Theorems.Thm_SaglamGV_muHat_tail_ks
import Theorems.Thm_SaglamGV_ks_tail_cutoff
import Theorems.Thm_SaglamGV_gammaKS_pos_and_lower
import Theorems.Thm_SaglamGV_vol_ge_choose_ge

set_option autoImplicit false
open SaglamGV

private lemma probY_mono {n : ℕ} {P Q : (Fin n → ZMod 2) → Prop}
    (h : ∀ y, P y → Q y) : probY P ≤ probY Q := by
  classical
  unfold probY avgY
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro y _
  by_cases hp : P y
  · simp [hp, h y hp]
  · simp only [hp, ↓reduceIte]
    split_ifs <;> norm_num

private lemma moment_decay (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (hgamma : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 - ε →
      c * ρ * Real.logb 2 (1 / ρ) ≤ gammaKS ρ)
    (n w : ℕ) (hn : 2 ≤ n) (hw : 1 ≤ w)
    (hl : (4 / c) * Real.logb 2 n ≤ w)
    (hu : (w : ℝ) ≤ (1 / 2 - ε) * n) :
    avgY (fun y ↦ |muHat n (w + 1) y| ^ 3) ≤
      1 / ((vol n (w + 1) : ℝ) * (n : ℝ) ^ 3) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hp : 0 < (w : ℝ) / n := div_pos hw0 hn0
  have hpε : (w : ℝ) / n ≤ 1 / 2 - ε := (div_le_iff₀ hn0).mpr hu
  have hp2 : (w : ℝ) / n ≤ 1 / 2 := by linarith
  have hwn : 2 * w ≤ n := by
    have hh := (div_le_iff₀ hn0).mp hp2
    exact_mod_cast (show (2 : ℝ) * w ≤ n by linarith)
  have hlog : 1 ≤ Real.logb 2 (1 / ((w : ℝ) / n)) := by
    calc
      1 = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        ((le_div_iff₀ hp).mpr (by linarith))
  have hgam : c * ((w : ℝ) / n) ≤ gammaKS ((w : ℝ) / n) :=
    (le_mul_of_one_le_right (by positivity) hlog).trans (hgamma _ hp hpε)
  have hngam : c * w ≤ (n : ℝ) * gammaKS ((w : ℝ) / n) := by
    calc
      _ = (n : ℝ) * (c * ((w : ℝ) / n)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hgam (le_of_lt hn0)
  have hlarge : 4 * Real.logb 2 n ≤ c * w := by
    calc
      _ = c * ((4 / c) * Real.logb 2 n) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl hc.le
  have he : -(n : ℝ) * gammaKS ((w : ℝ) / n) ≤ -4 * Real.logb 2 n := by
    linarith
  have hpow : (2 : ℝ) ^ (-(n : ℝ) * gammaKS ((w : ℝ) / n)) ≤
      1 / (n : ℝ) ^ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (-4 * Real.logb 2 n) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) he
      _ = ((2 : ℝ) ^ Real.logb 2 n) ^ (-4 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ = 1 / (n : ℝ) ^ 4 := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hn0]
        norm_num [Real.rpow_neg (le_of_lt hn0)]
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ n :=
    (Real.sqrt_le_left (le_of_lt hn0)).mpr (by nlinarith)
  have hmoment : (vol n (w + 1) : ℝ) *
      avgY (fun y ↦ |muHat n (w + 1) y| ^ 3) ≤ 1 / (n : ℝ) ^ 3 := by
    calc
      _ ≤ _ := muHat_third_moment_ks n w hn hw hwn
      _ ≤ (n : ℝ) * (1 / (n : ℝ) ^ 4) :=
        mul_le_mul hsqrt hpow (by positivity) (le_of_lt hn0)
      _ = 1 / (n : ℝ) ^ 3 := by field_simp
  have hv : (0 : ℝ) < vol n (w + 1) := by
    have hvol := (vol_ge_choose_ge n w (by omega) hw (by omega)).1
    have hchoose : (0 : ℝ) < n.choose w := by
      exact_mod_cast Nat.choose_pos (show w ≤ n by omega)
    exact hchoose.trans_le hvol
  apply (le_div_iff₀ (mul_pos hv (pow_pos hn0 3))).mpr
  have hh := (mul_le_mul_of_nonneg_right hmoment (pow_nonneg hn0.le 3))
  field_simp at hh
  nlinarith

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ L C : ℝ, ∃ N₀ : ℕ, ∀ n w : ℕ, N₀ ≤ n → L * Real.logb 2 n ≤ w →
      (w : ℝ) ≤ (1 / 2 - ε) * n →
      avgY (fun y ↦ |muHat n (w + 1) y| ^ 3) ≤
        C / ((vol n (w + 1) : ℝ) * (n : ℝ) ^ 3) ∧
      probY (fun y ↦ 1 / (n : ℝ) < |muHat n (w + 1) y|) ≤
        (2 : ℝ) ^ (-(n : ℝ) + 2 * n * Real.logb 2 n / w *
          Real.logb 2 (Real.exp 1 * w / Real.logb 2 n)) := by
  obtain ⟨c, hc, hgamma⟩ := gammaKS_pos_and_lower.2.2 ε hε
  obtain ⟨L, hL, N₀, hN₀, hcut⟩ := ks_tail_cutoff ε hε
  refine ⟨max L (4 / c), 1, N₀, ?_⟩
  intro n w hn hl hu
  have hn2 : 2 ≤ n := hN₀.trans hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by linarith)
  have hlL : L * Real.logb 2 n ≤ w :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog.le).trans hl
  have hlc : (4 / c) * Real.logb 2 n ≤ w :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog.le).trans hl
  have hw0 : (0 : ℝ) < w := (mul_pos hL hlog).trans_le hlL
  have hw : 1 ≤ w := by exact_mod_cast hw0
  have hwn : 2 * w ≤ n := by
    have hh : (2 : ℝ) * w ≤ n := by nlinarith
    exact_mod_cast hh
  constructor
  · exact moment_decay ε c hε hc hgamma n w hn2 hw hlc hu
  · let k : ℕ := ⌈(n : ℝ) * Real.logb 2 n / w⌉₊
    obtain ⟨hk, ht, he⟩ := hcut n w hn hlL hu
    calc
      _ ≤ probY (fun y ↦ Real.sqrt ((n : ℝ) + 1) *
          Real.exp (-2 * w * ((k : ℝ) / n)) < |muHat n (w + 1) y|) :=
        probY_mono (fun _ hy ↦ ht.trans_lt hy)
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (SelectiveDPT.H2 ((k : ℝ) / n) - 1)) :=
        muHat_tail_ks n w k hn2 hw hwn hk
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
