-- Prove2me | solution 1 for SaglamGV.vol_ge_choose_ge
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T16:43:26.531356+00:00
-- url     : https://prove2.me/submissions/5068b5c0-2e47-4ccd-a642-0f4b71736fa7

import Definitions.Def_SaglamGV_Code
import Definitions.Def_SelectiveDPT_H2
set_option autoImplicit false
open Finset SaglamGV

private lemma choose_le_volume (n w : ℕ) (hw : 1 ≤ w) : n.choose w ≤ vol n (w + 1) := by
  classical
  let f := fun S : Finset (Fin n) ↦ fun i ↦ if i ∈ S then (1 : ZMod 2) else 0
  have hnorm (S : Finset (Fin n)) : hammingNorm (f S) = S.card := by
    unfold hammingNorm
    congr 1
    ext i
    simp [f]
  have hmaps : Set.MapsTo f
      (↑((Finset.univ : Finset (Fin n)).powersetCard w) : Set (Finset (Fin n)))
      (↑(ballP n (w + 1)) : Set (Fin n → ZMod 2)) := by
    intro S hS
    have hc : S.card = w := (Finset.mem_powersetCard.mp hS).2
    change f S ∈ ballP n (w + 1)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hnorm, hc]
    omega
  have hinj : Function.Injective f := by
    intro S T hST
    ext i
    have h := congrFun hST i
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp_all [f]
  have h := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, vol] using h

private lemma binomial_mode (n w : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hnp : (n : ℝ) * p = w) (hwn : w ≤ n) :
    1 / ((n : ℝ) + 1) ≤ (n.choose w : ℝ) * p ^ w * (1 - p) ^ (n - w) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  let B := fun k : ℕ ↦ (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
  have hnon (k : ℕ) : 0 ≤ B k := by dsimp [B]; positivity
  have hrec (k : ℕ) (hk : k < n) :
      B (k + 1) * ((k : ℝ) + 1) * (1 - p) = B k * ((n : ℝ) - k) * p := by
    have hc : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
        (n.choose k : ℝ) * ((n : ℝ) - k) := by
      have h : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
          (n.choose k : ℝ) * (n - k : ℕ) := by
        exact_mod_cast Nat.choose_succ_right_eq n k
      simpa only [Nat.cast_sub hk.le] using h
    have he : n - k = (n - (k + 1)) + 1 := by omega
    dsimp [B]
    rw [he, pow_succ, pow_succ]
    linear_combination (p ^ k * p * (1 - p) ^ (n - (k + 1)) * (1 - p)) * hc
  have hinc (k : ℕ) (hk : k < w) : B k ≤ B (k + 1) := by
    have hkn : k < n := hk.trans_le hwn
    have h := hrec k hkn
    have hkR : (k : ℝ) + 1 ≤ w := by exact_mod_cast hk
    have hf : 0 < ((k : ℝ) + 1) * (1 - p) := by positivity
    have hd : ((k : ℝ) + 1) * (1 - p) ≤ ((n : ℝ) - k) * p := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hd (hnon k)
    apply (mul_le_mul_iff_right₀ hf).mp
    nlinarith only [h, hm]
  have hdec (k : ℕ) (hk : w ≤ k) : B (k + 1) ≤ B k := by
    by_cases hkn : k < n
    · have h := hrec k hkn
      have hkR : (w : ℝ) ≤ k := by exact_mod_cast hk
      have hf : 0 < ((k : ℝ) + 1) * (1 - p) := by positivity
      have hd : ((n : ℝ) - k) * p ≤ ((k : ℝ) + 1) * (1 - p) := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hd (hnon k)
      apply (mul_le_mul_iff_right₀ hf).mp
      nlinarith only [h, hm]
    · have hz : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simpa [B, hz] using hnon k
  have hleft (k : ℕ) (hk : k ≤ w) : B k ≤ B w := by
    exact Nat.decreasingInduction (n := w) (motive := fun k _ ↦ B k ≤ B w)
      (fun k hk ih ↦ (hinc k hk).trans ih) le_rfl hk
  have hmax (k : ℕ) : B k ≤ B w := by
    by_cases hk : k ≤ w
    · exact hleft k hk
    · exact (antitoneOn_nat_Ici_of_succ_le hdec)
        (show w ≤ w from le_rfl) (show w ≤ k by omega) (by omega)
  have hsum : ∑ k ∈ Finset.range (n + 1), B k = 1 := by
    have h := add_pow p (1 - p) n
    rw [show p + (1 - p) = 1 by ring, one_pow] at h
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hbound : 1 ≤ ((n : ℝ) + 1) * B w := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), B k := hsum.symm
      _ ≤ ∑ _k ∈ Finset.range (n + 1), B w := Finset.sum_le_sum (fun k _ ↦ hmax k)
      _ = _ := by simp
  apply (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).mpr
  nlinarith

private lemma entropy_mass (n w : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hnp : (n : ℝ) * p = w) (hwn : w ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) * SelectiveDPT.H2 p) =
      (p ^ w * (1 - p) ^ (n - w))⁻¹ := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hmass : 0 < p ^ w * (1 - p) ^ (n - w) := by positivity
  have hlog : Real.log (p ^ w * (1 - p) ^ (n - w)) =
      -(n : ℝ) * Real.binEntropy p := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    simp only [Real.binEntropy, Real.log_inv, Nat.cast_sub hwn]
    linear_combination -(Real.log p - Real.log (1 - p)) * hnp
  rw [Real.rpow_def_of_pos (by norm_num)]
  have he : Real.log 2 * ((n : ℝ) * SelectiveDPT.H2 p) =
      -Real.log (p ^ w * (1 - p) ^ (n - w)) := by
    rw [hlog]
    unfold SelectiveDPT.H2
    field_simp
  rw [he, Real.exp_neg, Real.exp_log hmass]

private lemma choose_ge_entropy (n w : ℕ) (hn : 1 ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) * SelectiveDPT.H2 ((w : ℝ) / n)) /
      ((n : ℝ) + 1) ≤ n.choose w := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hwe : w = n
  · subst w
    simp only [div_self hnR.ne', SelectiveDPT.H2, Real.binEntropy_one,
      zero_div, mul_zero, Real.rpow_zero, Nat.choose_self, Nat.cast_one]
    apply div_le_one_of_le₀
    · have := Nat.cast_nonneg (α := ℝ) n; linarith
    · positivity
  · let p : ℝ := w / n
    have hp : 0 < p := div_pos (by exact_mod_cast hw) hnR
    have hp1 : p < 1 := (div_lt_one hnR).mpr (by exact_mod_cast lt_of_le_of_ne hwn hwe)
    have hnp : (n : ℝ) * p = w := by dsimp [p]; field_simp
    have hmode := binomial_mode n w p hp hp1 hnp hwn
    have hmass : 0 < p ^ w * (1 - p) ^ (n - w) := by
      have hq : 0 < 1 - p := sub_pos.mpr hp1
      positivity
    rw [entropy_mass n w p hp hp1 hnp hwn]
    apply (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).mpr
    apply (inv_le_iff_one_le_mul₀ hmass).mpr
    have h := (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).mp hmode
    nlinarith

theorem solution (n w : ℕ) (hn : 1 ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n) :
    (n.choose w : ℝ) ≤ vol n (w + 1) ∧
      (2 : ℝ) ^ ((n : ℝ) * SelectiveDPT.H2 ((w : ℝ) / n)) /
        ((n : ℝ) + 1) ≤ n.choose w := by
  constructor
  · exact_mod_cast choose_le_volume n w hw
  · exact choose_ge_entropy n w hn hw hwn
