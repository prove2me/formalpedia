-- Prove2me | solution 1 for SaglamGV.redund_theta
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T10:15:38.04381+00:00
-- url     : https://prove2.me/submissions/0f67f1df-4eb1-488a-8e51-184873c00b40

import Definitions.Def_SaglamGV_Params
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

private lemma volume_entropy (n w : ℕ) (p : ℝ) (hp : 0 < p) (hp2 : p < 1 / 2)
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

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ n w : ℕ, 1 ≤ n → 1 ≤ w → (w : ℝ) ≤ (1 / 2 - ε) * n →
      a * n ≤ SaglamGV.redund n (w + 1) ∧
        SaglamGV.redund n (w + 1) ≤ n * Real.log 2 := by
  by_cases hε2 : ε < 1 / 2
  · let p := 1 / 2 - ε
    have hp : 0 < p := by dsimp [p]; linarith
    have hp2 : p < 1 / 2 := by dsimp [p]; linarith
    have hgap : 0 < Real.log 2 - Real.binEntropy p := by
      apply sub_pos.mpr
      apply Real.binEntropy_lt_log_two.mpr
      norm_num
      linarith
    refine ⟨Real.log 2 - Real.binEntropy p, hgap, ?_⟩
    intro n w hn hw hwp
    have hv : 0 < SaglamGV.vol n (w + 1) := by
      classical
      let i : Fin n := ⟨0, by omega⟩
      have hi : hammingNorm (Pi.single i 1 : Fin n → ZMod 2) = 1 := by
        simp only [hammingNorm, Pi.single_apply]
        have hfilter : (Finset.univ.filter fun j : Fin n ↦
            (ite (j = i) (1 : ZMod 2) 0) ≠ 0) = {i} := by
          ext j
          by_cases hj : j = i <;> simp [hj]
        rw [hfilter, Finset.card_singleton]
      apply Finset.card_pos.mpr
      refine ⟨Pi.single i 1, ?_⟩
      simp only [SaglamGV.ballP, Finset.mem_filter, Finset.mem_univ, true_and, hi]
      omega
    have hvR : (0 : ℝ) < SaglamGV.vol n (w + 1) := by exact_mod_cast hv
    have hv1 : (1 : ℝ) ≤ SaglamGV.vol n (w + 1) := by exact_mod_cast hv
    have hlogV : Real.log (SaglamGV.vol n (w + 1) : ℝ) ≤
        (n : ℝ) * Real.binEntropy p := by
      exact (Real.log_le_iff_le_exp hvR).mpr (volume_entropy n w p hp hp2 hwp)
    have hR : SaglamGV.redund n (w + 1) =
        n * Real.log 2 - Real.log (SaglamGV.vol n (w + 1) : ℝ) := by
      rw [SaglamGV.redund, Real.log_div (by positivity) (ne_of_gt hvR), Real.log_pow]
    rw [hR]
    constructor
    · nlinarith
    · linarith [Real.log_nonneg hv1]
  · refine ⟨1, by norm_num, ?_⟩
    intro n w hn hw hwp
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have hnp : (1 / 2 - ε) * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hnR
    linarith
