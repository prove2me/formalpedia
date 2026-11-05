-- Prove2me | solution 1 for SlowConvergence.Newton.bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:35:36.449817+00:00
-- url     : https://prove2.me/submissions/5c60cc02-f47b-40d1-ac2c-70e6030e300c

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

set_option autoImplicit false
open scoped RealInnerProductSpace
open SlowConvergence.Newton

lemma bb_eta_pos {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) : 0 < eta τ := by
  unfold eta
  apply div_pos h0; linarith

lemma bb_summable {t : ℝ} (ht : 1 < t) : Summable (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ t) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr ht)
  refine h.congr (fun n => ?_)
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow]

lemma bb_partial_le {t : ℝ} (ht : 1 < t) (k : ℕ) :
    ∑ j ∈ Finset.range k, (1 / ((j : ℝ) + 1)) ^ t ≤ zetaR t := by
  unfold zetaR
  exact (bb_summable ht).sum_le_tsum _ (fun j _ => by positivity)

lemma bb_f21 (τ : ℝ) (k : ℕ) :
    f21knot τ k = 1 / 2 * (zetaR (1 + 2 * eta τ)
      - ∑ j ∈ Finset.range k, (1 / ((j : ℝ) + 1)) ^ (1 + 2 * eta τ)) := by
  induction k with
  | zero => simp [f21knot]
  | succ k ih => rw [f21knot, ih, Finset.sum_range_succ]; ring

lemma bb_f22 (k : ℕ) :
    f22knot k = 1 / 2 * (zetaR 2 - ∑ j ∈ Finset.range k, (1 / ((j : ℝ) + 1)) ^ (2 : ℝ)) := by
  induction k with
  | zero => simp [f22knot]
  | succ k ih =>
    rw [f22knot, ih, Finset.sum_range_succ]
    have : (1 / ((k : ℝ) + 1)) ^ (2 : ℝ) = (1 / ((k : ℝ) + 1)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [this]; ring

lemma bb_fk (τ : ℝ) (k : ℕ) : fk τ k = f21knot τ k + f22knot k := by
  induction k with
  | zero => simp [fk, f21knot, f22knot]; ring
  | succ k ih => rw [fk, f21knot, f22knot, ih]; ring

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 ≤ f21knot τ k ∧ 0 ≤ f22knot k ∧ fk τ k = f21knot τ k + f22knot k ∧ 0 ≤ fk τ k ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (mu τ k), 0 ≤ p τ k t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q k t) := by
  have hη := bb_eta_pos hτ0 hτ1
  have h1 : 0 ≤ f21knot τ k := by
    rw [bb_f21]
    have := bb_partial_le (t := 1 + 2 * eta τ) (by linarith) k
    linarith
  have h2 : 0 ≤ f22knot k := by
    rw [bb_f22]
    have := bb_partial_le (t := 2) (by norm_num) k
    linarith
  refine ⟨h1, h2, bb_fk τ k, by rw [bb_fk]; linarith, ?_, ?_⟩
  · intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hmu : 0 < mu τ k := by unfold mu; exact Real.rpow_pos_of_pos (by positivity) _
    have hsq : (1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ) = mu τ k ^ 2 := by
      unfold mu
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1; push_cast; ring
    have hpsi : 0 ≤ SlowConvergence.SteepestDescent.psi τ k := by
      unfold SlowConvergence.SteepestDescent.psi
      exact Real.rpow_nonneg (by positivity) _
    have key : p τ k t * mu τ k ^ 3 = 1 / 2 * mu τ k ^ 3 * (mu τ k - t) ^ 2
        + SlowConvergence.SteepestDescent.psi τ k * t ^ 3 * (mu τ k - t) * (4 * mu τ k - 3 * t) := by
      unfold p phi
      rw [hsq]
      field_simp
      ring
    set m := mu τ k
    set ψ := SlowConvergence.SteepestDescent.psi τ k
    have hr : 0 ≤ 1 / 2 * m ^ 3 * (m - t) ^ 2 + ψ * t ^ 3 * (m - t) * (4 * m - 3 * t) := by
      have a : 0 ≤ m - t := by linarith
      have b : 0 ≤ 4 * m - 3 * t := by linarith
      have : 0 ≤ ψ * t ^ 3 * (m - t) * (4 * m - 3 * t) := by positivity
      have : 0 ≤ 1 / 2 * m ^ 3 * (m - t) ^ 2 := by positivity
      linarith
    rw [← key] at hr
    exact nonneg_of_mul_nonneg_left hr (by positivity)
  · intro s hs
    obtain ⟨h0, h1⟩ := hs
    have key : q k s = 1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2 * (1 - s) ^ 2 * (1 - s ^ 3)
        + 1 / 2 * (1 / ((k : ℝ) + 2)) ^ 2 * s ^ 3 * (1 - s) * (9 - 7 * s) := by
      unfold q; ring
    rw [key]
    have a : 0 ≤ 1 - s := by linarith
    have b : 0 ≤ 1 - s ^ 3 := by nlinarith [pow_le_one₀ h0 h1 (n := 3)]
    have c : 0 ≤ 9 - 7 * s := by linarith
    positivity
