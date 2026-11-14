-- Prove2me | solution 1 for SaglamGV.parseval_muHat_and_log_vol
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T17:09:27.173633+00:00
-- url     : https://prove2.me/submissions/34818437-376f-4f0c-bf08-8ffd2084285f

import Theorems.Thm_SaglamGV_vol_ge_choose_ge
import Theorems.Thm_SaglamGV_zeroSumProb_eq_avg_muHat_pow
set_option autoImplicit false
open Finset

private lemma sum_weight (n : ℕ) (x : Fin n → ZMod 2) (a b : ℝ) :
    (∑ i, if x i = 0 then a else b) = n * a + (hammingNorm x : ℝ) * (b - a) := by
  classical
  have h (i : Fin n) : (if x i = 0 then a else b) =
      a + (if x i ≠ 0 then b - a else 0) := by split_ifs <;> simp_all
  simp_rw [h]
  simp [Finset.sum_add_distrib, Finset.sum_ite, hammingNorm]
  ring

private lemma mass_sum (n : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∑ x : Fin n → ZMod 2,
      Real.exp ((n : ℝ) * Real.log (1 - p) +
        (hammingNorm x : ℝ) * (Real.log p - Real.log (1 - p)))) = 1 := by
  have hsum : (∑ z : ZMod 2, if z = 0 then 1 - p else p) = 1 := by
    have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [h]
    norm_num
  calc
    _ = ∑ x : Fin n → ZMod 2, ∏ i, (if x i = 0 then 1 - p else p) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← sum_weight n x (Real.log (1 - p)) (Real.log p), Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> simp [Real.exp_log hp, Real.exp_log (sub_pos.mpr hp1)]
    _ = (∑ z : ZMod 2, if z = 0 then 1 - p else p) ^ n :=
      (Fintype.sum_pow (fun z : ZMod 2 ↦ if z = 0 then 1 - p else p) n).symm
    _ = 1 := by rw [hsum, one_pow]

private lemma volume_entropy (n w : ℕ) (p : ℝ) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (hw : (w : ℝ) ≤ p * n) :
    (SaglamGV.vol n (w + 1) : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy p) := by
  classical
  have hp1 : p < 1 := by linarith
  have hlog : Real.log p - Real.log (1 - p) ≤ 0 := by
    apply sub_nonpos.mpr
    apply Real.log_le_log hp
    linarith
  have heq : (n : ℝ) * Real.log (1 - p) + (p * n) *
      (Real.log p - Real.log (1 - p)) = -(n : ℝ) * Real.binEntropy p := by
    simp only [Real.binEntropy, Real.log_inv]
    ring
  have hmass (x : Fin n → ZMod 2) (hx : x ∈ SaglamGV.ballP n (w + 1)) :
      Real.exp (-(n : ℝ) * Real.binEntropy p) ≤
        Real.exp ((n : ℝ) * Real.log (1 - p) +
          (hammingNorm x : ℝ) * (Real.log p - Real.log (1 - p))) := by
    apply Real.exp_le_exp.mpr
    rw [← heq]
    apply add_le_add_right
    apply mul_le_mul_of_nonpos_right _ hlog
    have hweight : hammingNorm x ≤ w := by
      simp only [SaglamGV.ballP, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      omega
    exact (Nat.cast_le.mpr hweight).trans hw
  have hbound : (SaglamGV.vol n (w + 1) : ℝ) *
      Real.exp (-(n : ℝ) * Real.binEntropy p) ≤ 1 := by
    calc
      _ = ∑ _x ∈ SaglamGV.ballP n (w + 1),
          Real.exp (-(n : ℝ) * Real.binEntropy p) := by
        simp [SaglamGV.vol]
      _ ≤ ∑ x ∈ SaglamGV.ballP n (w + 1),
          Real.exp ((n : ℝ) * Real.log (1 - p) +
            (hammingNorm x : ℝ) * (Real.log p - Real.log (1 - p))) :=
        Finset.sum_le_sum hmass
      _ ≤ ∑ x : Fin n → ZMod 2,
          Real.exp ((n : ℝ) * Real.log (1 - p) +
            (hammingNorm x : ℝ) * (Real.log p - Real.log (1 - p))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intros
        positivity
      _ = 1 := mass_sum n p hp hp1
  have hexp := Real.exp_pos (-(n : ℝ) * Real.binEntropy p)
  calc
    _ ≤ 1 / Real.exp (-(n : ℝ) * Real.binEntropy p) :=
      (le_div_iff₀ hexp).mpr hbound
    _ = Real.exp ((n : ℝ) * Real.binEntropy p) := by rw [neg_mul, Real.exp_neg]; simp

private lemma second_moment (n d : ℕ) :
    SaglamGV.avgY (fun y ↦ SaglamGV.muHat n d y ^ 2) = 1 / (SaglamGV.vol n d : ℝ) := by
  classical
  rw [← (SaglamGV.zeroSumProb_eq_avg_muHat_pow n d).1 2]
  have he : (Finset.univ.filter (fun t : Fin 2 → (Fin n → ZMod 2) ↦
      (∀ i, t i ∈ SaglamGV.ballP n d) ∧ ∑ i, t i = 0)) =
      (SaglamGV.ballP n d).image (fun x ↦ fun _ : Fin 2 ↦ x) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hb, hs⟩
      have ht : t 1 = t 0 := by
        rw [Fin.sum_univ_two] at hs
        have hh := eq_neg_of_add_eq_zero_left hs
        funext i
        simpa only [Pi.neg_apply, CharTwo.neg_eq] using (congrFun hh i).symm
      refine ⟨t 0, hb 0, ?_⟩
      funext i
      fin_cases i <;> simp [ht]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun _ ↦ hx, ?_⟩
      rw [Fin.sum_univ_two]
      ext i
      exact CharTwo.add_self_eq_zero (x i)
  have hi : Function.Injective (fun x : Fin n → ZMod 2 ↦ fun _ : Fin 2 ↦ x) := by
    intro x y h
    exact congrFun h 0
  unfold SaglamGV.zeroSumProb
  rw [he, Finset.card_image_of_injective _ hi]
  change (SaglamGV.vol n d : ℝ) / (SaglamGV.vol n d : ℝ) ^ 2 = _
  by_cases h : (SaglamGV.vol n d : ℝ) = 0
  · simp [h]
  · field_simp

private lemma log_volume (n w : ℕ) (hn : 2 ≤ n) (hw : 1 ≤ w) (hwn : 2 * w ≤ n) :
    |Real.logb 2 (SaglamGV.vol n (w + 1)) -
      n * SelectiveDPT.H2 ((w : ℝ) / n)| ≤ 2 * Real.logb 2 n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hwp : (2 : ℝ) * w ≤ n := by exact_mod_cast hwn
  have hp : 0 < (w : ℝ) / n := div_pos hw0 hn0
  have hp2 : (w : ℝ) / n ≤ 1 / 2 := (div_le_iff₀ hn0).mpr (by linarith)
  have hlow := SaglamGV.vol_ge_choose_ge n w (by omega) hw (by omega)
  have hv : (0 : ℝ) < SaglamGV.vol n (w + 1) :=
    lt_of_lt_of_le (by exact_mod_cast Nat.choose_pos (show w ≤ n by omega)) hlow.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : (2 : ℝ) ^ ((n : ℝ) * SelectiveDPT.H2 ((w : ℝ) / n)) =
      Real.exp ((n : ℝ) * Real.binEntropy ((w : ℝ) / n)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    unfold SelectiveDPT.H2
    field_simp
  have hlo := hlow.2.trans hlow.1
  rw [he] at hlo
  have hlnlo := Real.log_le_log (div_pos (Real.exp_pos _) (by linarith)) hlo
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by positivity), Real.log_exp] at hlnlo
  have hlnhi := (Real.log_le_iff_le_exp hv).mpr
    (volume_entropy n w ((w : ℝ) / n) hp hp2 (by
      rw [div_mul_cancel₀ _ (ne_of_gt hn0)]))
  have hlnn : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
    have hh : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hh' := Real.log_le_log (show (0 : ℝ) < n + 1 by linarith) hh
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh'
  have habs : |Real.log (SaglamGV.vol n (w + 1) : ℝ) -
      n * Real.binEntropy ((w : ℝ) / n)| ≤ 2 * Real.log n := by
    apply abs_le.mpr
    constructor <;> linarith [Real.log_nonneg (show (1 : ℝ) ≤ n by linarith)]
  simp only [Real.logb, SelectiveDPT.H2]
  rw [← mul_div_assoc, ← sub_div, abs_div, abs_of_pos hlog2]
  simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right habs (le_of_lt hlog2))

theorem solution :
    (∀ n d : ℕ, 2 ≤ d → SaglamGV.avgY (fun y ↦ SaglamGV.muHat n d y ^ 2) =
      1 / (SaglamGV.vol n d : ℝ)) ∧
      ∃ C : ℝ, ∀ n w : ℕ, 2 ≤ n → 1 ≤ w → 2 * w ≤ n →
        |Real.logb 2 (SaglamGV.vol n (w + 1)) -
          n * SelectiveDPT.H2 ((w : ℝ) / n)| ≤ C * Real.logb 2 n := by
  exact ⟨fun n d _ ↦ second_moment n d, 2, log_volume⟩
