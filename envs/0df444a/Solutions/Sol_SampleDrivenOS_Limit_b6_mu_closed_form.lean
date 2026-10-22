-- Prove2me | solution 1 for SampleDrivenOS.Limit.b6_mu_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:04:09.308794+00:00
-- url     : https://prove2.me/submissions/f75a3427-6681-4210-b09d-189107c1428a

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
    ∀ k : ℕ, 3 ≤ k →
      mu (tSeq p α) k = p * (1 - α + α * p ^ (k - 2)) / ((k : ℝ) - 2) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  -- c m = p (1 - α + α p^m) / m
  set c : ℕ → ℝ := fun m => p * (1 - α + α * p ^ m) / (m : ℝ) with hc
  have hterm : ∀ i : ℕ,
      SampleDrivenOS.Structure.thresholdProd (tSeq p α) (i + (j + 3)) /
          tSeq p α (i + (j + 3)) ^ (i + (j + 3) - 1) *
        (1 / ((((i + (j + 3) : ℕ) : ℝ) - 2) * (((i + (j + 3) : ℕ) : ℝ) - 1)))
      = c (j + 1 + i) - c (j + 1 + i + 1) := by
    intro i
    have h := sdl_prod_id p α hp hα (i + j + 1)
    have e1 : i + (j + 3) = (i + j + 1) + 2 := by omega
    have e2 : i + (j + 3) - 1 = (i + j + 1) + 1 := by omega
    have e3 : j + 1 + i = i + j + 1 := by omega
    rw [e2, e1, h, sdl_gam_eq, e3]
    generalize hn : i + j + 1 = n
    have r1 : ((n + 2 : ℕ) : ℝ) - 2 = n := by push_cast; ring
    have r2 : ((n + 2 : ℕ) : ℝ) - 1 = (n : ℝ) + 1 := by push_cast; ring
    rw [r1, r2]
    simp only [hc]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hnn : ∀ i : ℕ, 0 ≤ SampleDrivenOS.Structure.thresholdProd (tSeq p α) (i + (j + 3)) /
          tSeq p α (i + (j + 3)) ^ (i + (j + 3) - 1) *
        (1 / ((((i + (j + 3) : ℕ) : ℝ) - 2) * (((i + (j + 3) : ℕ) : ℝ) - 1))) := by
    intro i
    have h := sdl_prod_id p α hp hα (i + j + 1)
    have e1 : i + (j + 3) = (i + j + 1) + 2 := by omega
    have e2 : i + (j + 3) - 1 = (i + j + 1) + 1 := by omega
    rw [e2, e1, h]
    have g := sdl_gam_pos p α hp hα (i + j + 1)
    have hh : (0:ℝ) < (((i + j + 1 + 2 : ℕ) : ℝ) - 2) * (((i + j + 1 + 2 : ℕ) : ℝ) - 1) := by
      push_cast
      have : (0:ℝ) ≤ i := Nat.cast_nonneg i
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    exact mul_nonneg (mul_nonneg hp.1.le g.le) (by positivity)
  have hlim : Tendsto c atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => p * (1 - α + α * p ^ m)) atTop (𝓝 (p * (1 - α + α * 0))) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one hp.1.le hp.2
      exact tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul this))
    have h2 : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have := h1.mul h2
    simp only [mul_zero] at this
    refine this.congr (fun m => ?_)
    simp only [hc]
    ring
  have hHas : HasSum (fun i : ℕ =>
      SampleDrivenOS.Structure.thresholdProd (tSeq p α) (i + (j + 3)) /
          tSeq p α (i + (j + 3)) ^ (i + (j + 3) - 1) *
        (1 / ((((i + (j + 3) : ℕ) : ℝ) - 2) * (((i + (j + 3) : ℕ) : ℝ) - 1)))) (c (j + 1)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    have hps : ∀ n : ℕ, ∑ i ∈ Finset.range n,
        SampleDrivenOS.Structure.thresholdProd (tSeq p α) (i + (j + 3)) /
          tSeq p α (i + (j + 3)) ^ (i + (j + 3) - 1) *
        (1 / ((((i + (j + 3) : ℕ) : ℝ) - 2) * (((i + (j + 3) : ℕ) : ℝ) - 1)))
        = c (j + 1) - c (j + 1 + n) := by
      intro n
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      have := Finset.sum_range_sub' (fun i => c (j + 1 + i)) n
      simp only [add_zero] at this
      exact this
    simp only [hps]
    have h3 : Tendsto (fun n : ℕ => c (j + 1 + n)) atTop (𝓝 0) := by
      have := hlim.comp (tendsto_atTop_mono (fun n : ℕ => (by omega : n ≤ j + 1 + n)) tendsto_id)
      exact this
    have := (tendsto_const_nhds (x := c (j + 1))).sub h3
    simpa using this
  rw [show mu (tSeq p α) (j + 3) = ∑' i : ℕ,
      SampleDrivenOS.Structure.thresholdProd (tSeq p α) (i + (j + 3)) /
          tSeq p α (i + (j + 3)) ^ (i + (j + 3) - 1) *
        (1 / ((((i + (j + 3) : ℕ) : ℝ) - 2) * (((i + (j + 3) : ℕ) : ℝ) - 1))) from rfl]
  rw [hHas.tsum_eq]
  simp only [hc]
  push_cast
  rw [show ((j:ℝ) + 3 - 2) = (j:ℝ) + 1 by ring]
