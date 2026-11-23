-- Prove2me | solution 2 for SaglamGV.lemma_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T05:45:48.230921+00:00
-- url     : https://prove2.me/submissions/977655bf-4303-4024-995d-a997b20ec101
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Walk
import Definitions.Def_SaglamGV_Fourier
import Theorems.Thm_SaglamGV_muHat_third_moment_ks
import Theorems.Thm_SaglamGV_muHat_tail_ks
import Theorems.Thm_SaglamGV_ks_tail_cutoff
import Theorems.Thm_SaglamGV_gammaKS_pos_and_lower
import Theorems.Thm_SaglamGV_vol_ge_choose_ge

open SaglamGV

theorem probY_mono_aux {n : ℕ} {P Q : (Fin n → ZMod 2) → Prop} (h : ∀ y, P y → Q y) :
    probY P ≤ probY Q := by
  classical
  unfold probY avgY
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro y _
  by_cases hp : P y
  · simp [hp, h y hp]
  · simp only [hp, if_false]; split_ifs <;> norm_num

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ L C : ℝ, ∃ N₀ : ℕ, ∀ n w : ℕ, N₀ ≤ n → L * Real.logb 2 n ≤ w → (w : ℝ) ≤ (1 / 2 - ε) * n →
      avgY (fun y => |muHat n (w + 1) y| ^ 3) ≤ C / ((vol n (w + 1) : ℝ) * (n : ℝ) ^ 3) ∧
      probY (fun y => 1 / (n : ℝ) < |muHat n (w + 1) y|) ≤
        (2 : ℝ) ^ (-(n : ℝ) + 2 * n * Real.logb 2 n / w *
          Real.logb 2 (Real.exp 1 * w / Real.logb 2 n)) := by
  obtain ⟨_, _, hlow⟩ := gammaKS_pos_and_lower
  obtain ⟨c, hc, hcγ⟩ := hlow ε hε
  obtain ⟨L1, hL1, N1, hN1, hcut⟩ := ks_tail_cutoff ε hε
  refine ⟨max L1 (4 / c), 1, N1, fun n w hn hLw hwε => ?_⟩
  have hn2 : 2 ≤ n := le_trans hN1 hn
  have hn2' : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hlogn : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hn2'
  have hLw1 : L1 * Real.logb 2 n ≤ w :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hLw
  have hLw2 : 4 / c * Real.logb 2 n ≤ w :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)) hLw
  have hwpos : (0:ℝ) < w := lt_of_lt_of_le (mul_pos hL1 (by linarith)) hLw1
  have hw : 1 ≤ w := by exact_mod_cast hwpos
  have hw1 : (1:ℝ) ≤ w := by exact_mod_cast hw
  have hnpos : (0:ℝ) < n := by linarith
  have hε' : 0 < (1:ℝ) / 2 - ε := by nlinarith
  have hwn : 2 * w ≤ n := by
    have : (2 * w : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hwn' : (2 * w : ℝ) ≤ n := by exact_mod_cast hwn
  have hVpos : (0:ℝ) < vol n (w + 1) := by
    have h := (vol_ge_choose_ge n w (by omega) hw (by omega)).1
    have : (0:ℝ) < n.choose w := by
      exact_mod_cast Nat.choose_pos (by omega)
    linarith
  constructor
  · have h3 := muHat_third_moment_ks n w hn2 hw hwn
    set ρ : ℝ := (w : ℝ) / n with hρ
    have hρpos : 0 < ρ := by positivity
    have hρle : ρ ≤ 1 / 2 - ε := by
      rw [hρ, div_le_iff₀ hnpos]; exact hwε
    have hγ := hcγ ρ hρpos hρle
    have hlg : 1 ≤ Real.logb 2 (1 / ρ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
      simp only [Real.rpow_one]
      rw [hρ, one_div, inv_div, le_div_iff₀ hwpos]; linarith
    have hnγ : 4 * Real.logb 2 n ≤ n * gammaKS ρ := by
      have h1 : c * ρ * 1 ≤ gammaKS ρ :=
        le_trans (mul_le_mul_of_nonneg_left hlg (by positivity)) hγ
      have h2 : (n:ℝ) * (c * ρ * 1) = c * w := by
        rw [hρ]; field_simp
      have h3 : 4 * Real.logb 2 n ≤ c * w := by
        have := mul_le_mul_of_nonneg_left hLw2 hc.le
        have e : c * (4 / c * Real.logb 2 n) = 4 * Real.logb 2 n := by field_simp
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hnpos.le]
    have hpow : (2:ℝ) ^ (-(n : ℝ) * gammaKS ρ) ≤ ((n:ℝ) ^ 4)⁻¹ := by
      calc (2:ℝ) ^ (-(n : ℝ) * gammaKS ρ) ≤ (2:ℝ) ^ (-4 * Real.logb 2 n) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = ((n:ℝ) ^ 4)⁻¹ := by
            rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hnpos,
              Real.rpow_neg hnpos.le]
            norm_num
    have hsq : Real.sqrt ((n:ℝ) + 1) ≤ n := by
      rw [Real.sqrt_le_left hnpos.le]; nlinarith
    have hV : (vol n (w + 1) : ℝ) * avgY (fun y => |muHat n (w + 1) y| ^ 3) ≤ ((n:ℝ) ^ 3)⁻¹ := by
      refine le_trans h3 ?_
      calc Real.sqrt ((n:ℝ) + 1) * (2:ℝ) ^ (-(n : ℝ) * gammaKS ρ)
          ≤ n * ((n:ℝ) ^ 4)⁻¹ :=
            mul_le_mul hsq hpow (by positivity) hnpos.le
        _ = ((n:ℝ) ^ 3)⁻¹ := by field_simp
    have hn3 : (0:ℝ) < (n:ℝ) ^ 3 := by positivity
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hV hn3.le
    rw [inv_mul_cancel₀ hn3.ne'] at this
    linarith
  · obtain ⟨hk1, hk2, hk3⟩ := hcut n w hn hLw1 hwε
    set k : ℕ := ⌈(n : ℝ) * Real.logb 2 n / w⌉₊ with hk
    have ht := muHat_tail_ks n w k hn2 hw hwn hk1
    refine le_trans (probY_mono_aux (fun y hy => lt_of_le_of_lt hk2 hy)) (le_trans ht ?_)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hk3

