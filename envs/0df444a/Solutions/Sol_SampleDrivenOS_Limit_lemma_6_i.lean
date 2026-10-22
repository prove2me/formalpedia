-- Prove2me | solution 1 for SampleDrivenOS.Limit.lemma_6_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:09:41.259271+00:00
-- url     : https://prove2.me/submissions/84371982-4207-41a9-8c66-d177334c57b4

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting
set_option autoImplicit false
open MeasureTheory Filter Topology SampleDrivenOS.Limit

section sdl_helpers

lemma sdl_gam_eq (p α : ℝ) (j : ℕ) :
    gammaK p α (j + 1) = 1 - α + α * (((j : ℝ) + 1) * p ^ j - (j : ℝ) * p ^ (j + 1)) := by
  simp only [gammaK, Nat.add_sub_cancel]
  push_cast
  ring

lemma sdl_gam_pos (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) (j : ℕ) :
    0 < gammaK p α (j + 1) := by
  rw [sdl_gam_eq]
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hα0, hα1⟩ := hα
  have h1 : 0 ≤ p ^ j := pow_nonneg hp0.le j
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have h2 : 0 ≤ ((j : ℝ) + 1) * p ^ j - (j : ℝ) * p ^ (j + 1) := by
    have : ((j : ℝ) + 1) * p ^ j - (j : ℝ) * p ^ (j + 1) = p ^ j * (1 + j * (1 - p)) := by ring
    rw [this]
    exact mul_nonneg h1 (by nlinarith)
  nlinarith [mul_nonneg hα0.le h2]

lemma sdl_gam_step (p α : ℝ) (j : ℕ) :
    gammaK p α (j + 2) = gammaK p α (j + 1) - α * ((j : ℝ) + 1) * p ^ j * (1 - p) ^ 2 := by
  rw [show j + 2 = (j + 1) + 1 from rfl, sdl_gam_eq, sdl_gam_eq]
  push_cast
  ring

lemma sdl_t_pos (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∀ k : ℕ, 0 < tSeq p α (k + 1) ∧ 0 < tSeq p α (k + 2) := by
  intro k
  induction k with
  | zero =>
    refine ⟨hp.1, ?_⟩
    show 0 < p * Real.exp (α * (1 - p) ^ 2 / p)
    exact mul_pos hp.1 (Real.exp_pos _)
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    show 0 < tSeq p α (k + 2) * (gammaK p α (k + 1) / gammaK p α (k + 2)) ^ (1 / ((k : ℝ) + 1))
    exact mul_pos ih.2 (Real.rpow_pos_of_pos (div_pos (sdl_gam_pos p α hp hα k)
      (sdl_gam_pos p α hp hα (k + 1))) _)

lemma sdl_t_rec (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) (k : ℕ) :
    tSeq p α (k + 3) ^ (k + 1) =
      tSeq p α (k + 2) ^ (k + 1) * (gammaK p α (k + 1) / gammaK p α (k + 2)) := by
  have e : tSeq p α (k + 3) = tSeq p α (k + 2) *
      (gammaK p α (k + 1) / gammaK p α (k + 2)) ^ (1 / ((k : ℝ) + 1)) := rfl
  have hx : ((gammaK p α (k + 1) / gammaK p α (k + 2)) ^ (1 / ((k : ℝ) + 1))) ^ (k + 1) =
      gammaK p α (k + 1) / gammaK p α (k + 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul
      (div_pos (sdl_gam_pos p α hp hα k) (sdl_gam_pos p α hp hα (k + 1))).le]
    have : 1 / ((k : ℝ) + 1) * ((k + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  rw [e, mul_pow, hx]

lemma sdl_prod_succ (t : ℕ → ℝ) (m : ℕ) :
    SampleDrivenOS.Structure.thresholdProd t (m + 1) =
      SampleDrivenOS.Structure.thresholdProd t m * t (m + 1) := by
  unfold SampleDrivenOS.Structure.thresholdProd
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma sdl_prod_id (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∀ k : ℕ, SampleDrivenOS.Structure.thresholdProd (tSeq p α) (k + 2) /
        tSeq p α (k + 2) ^ (k + 1) = p * gammaK p α (k + 1) := by
  intro k
  induction k with
  | zero =>
    have h2 := (sdl_t_pos p α hp hα 0).2
    have e1 : gammaK p α 1 = 1 := by simp [gammaK]
    have e2 : SampleDrivenOS.Structure.thresholdProd (tSeq p α) 2 =
        tSeq p α 1 * tSeq p α 2 := by
      unfold SampleDrivenOS.Structure.thresholdProd
      simp [Finset.prod_Icc_succ_top]
    rw [e1, e2]
    show tSeq p α 1 * tSeq p α 2 / tSeq p α 2 ^ 1 = p * 1
    rw [pow_one, mul_div_assoc, div_self h2.ne', mul_one, mul_one]
    rfl
  | succ k ih =>
    have hpos2 := (sdl_t_pos p α hp hα (k + 1)).2   -- t (k+3)
    have hpos1 := (sdl_t_pos p α hp hα (k + 1)).1   -- t (k+2)
    have g1 := sdl_gam_pos p α hp hα k
    have g2 := sdl_gam_pos p α hp hα (k + 1)
    have hrec := sdl_t_rec p α hp hα k
    have hP : SampleDrivenOS.Structure.thresholdProd (tSeq p α) (k + 1 + 2) =
        SampleDrivenOS.Structure.thresholdProd (tSeq p α) (k + 2) * tSeq p α (k + 3) :=
      sdl_prod_succ (tSeq p α) (k + 2)
    rw [hP]
    have hpw : tSeq p α (k + 1 + 2) ^ (k + 1 + 1) =
        tSeq p α (k + 3) ^ (k + 1) * tSeq p α (k + 3) := by
      rw [show k + 1 + 2 = k + 3 from rfl]; ring
    rw [hpw, hrec]
    have ih' := ih
    rw [div_eq_iff (pow_pos hpos1 _).ne'] at ih'
    rw [show k + 1 + 1 = k + 2 from rfl, show (k + 1 + 1 : ℕ) = k + 2 from rfl]
    have hT : SampleDrivenOS.Structure.thresholdProd (tSeq p α) (k + 2) =
        p * gammaK p α (k + 1) * tSeq p α (k + 2) ^ (k + 1) := ih'
    rw [hT]
    have hq := pow_pos hpos1 (k + 1)
    field_simp

end sdl_helpers

theorem solution (p α : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hα : α ∈ Set.Ioo (0:ℝ) 1) :
    ∀ k : ℕ, 1 ≤ k → tSeq p α k ≤ tSeq p α (k + 1) := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases m with _ | m
  · -- t 1 = p ≤ t 2
    show p ≤ p * Real.exp (α * (1 - p) ^ 2 / p)
    have h1 : 1 ≤ Real.exp (α * (1 - p) ^ 2 / p) := by
      apply Real.one_le_exp
      exact div_nonneg (mul_nonneg hα.1.le (sq_nonneg _)) hp.1.le
    nlinarith [hp.1]
  · -- t (m+2) ≤ t (m+3)
    show tSeq p α (m + 2) ≤ tSeq p α (m + 2) *
      (gammaK p α (m + 1) / gammaK p α (m + 2)) ^ (1 / ((m : ℝ) + 1))
    have hpos := (sdl_t_pos p α hp hα m).2
    have g1 := sdl_gam_pos p α hp hα m
    have g2 := sdl_gam_pos p α hp hα (m + 1)
    have hle : gammaK p α (m + 2) ≤ gammaK p α (m + 1) := by
      rw [sdl_gam_step]
      have : 0 ≤ α * ((m : ℝ) + 1) * p ^ m * (1 - p) ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg hα.1.le (by positivity)) (pow_nonneg hp.1.le m))
          (sq_nonneg _)
      linarith
    have hr : 1 ≤ gammaK p α (m + 1) / gammaK p α (m + 2) := by
      rw [le_div_iff₀ g2]; linarith
    have hx : 1 ≤ (gammaK p α (m + 1) / gammaK p α (m + 2)) ^ (1 / ((m : ℝ) + 1)) :=
      Real.one_le_rpow hr (by positivity)
    nlinarith
