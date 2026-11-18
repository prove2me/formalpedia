-- Prove2me | solution 2 for QuantumLTF.Majority.harmonic_kernel_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T14:13:40.825522+00:00
-- url     : https://prove2.me/submissions/66d4899b-7835-4edc-beac-9de754adac26

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators

theorem solution : ∃ H : ℝ, 0 < H ∧ ∀ r : ℕ, 3 ≤ r →
    ∑ t : Fin (r+1), (r : ℝ) /
      (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) ≤ H * Real.log r := by
  refine ⟨6, by norm_num, ?_⟩
  intro r hr
  have hr0 : (0 : ℝ) < r := by positivity
  have hlog : 1 < Real.log (r : ℝ) := by
    have h3r : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have hlog3 : 1 < Real.log (3 : ℝ) :=
      lt_trans (by norm_num) Real.log_three_gt_d9
    exact hlog3.trans_le
      (Real.strictMonoOn_log.monotoneOn (by norm_num) hr0 h3r)
  have hterm (t : Fin (r + 1)) :
      (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) ≤
        ((t : ℕ) + 1 : ℝ)⁻¹ + (r - (t : ℕ) + 1 : ℝ)⁻¹ := by
    have ht : (t : ℕ) ≤ r := Nat.le_of_lt_succ t.isLt
    have ha : (0 : ℝ) < (t : ℕ) + 1 := by positivity
    have hb : (0 : ℝ) < r - (t : ℕ) + 1 := by
      norm_num [Nat.cast_sub ht]
      exact_mod_cast (show 0 < r - (t : ℕ) + 1 by omega)
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_sub ht]
    rw [div_le_iff₀ (mul_pos ha hb)]
    field_simp
    norm_num [Nat.cast_sub ht]
    exact_mod_cast (show r ≤ (r - (t : ℕ) + 1) + ((t : ℕ) + 1) by omega)
  calc
    _ ≤ ∑ t : Fin (r+1),
        (((t : ℕ) + 1 : ℝ)⁻¹ + (r - (t : ℕ) + 1 : ℝ)⁻¹) :=
      Finset.sum_le_sum fun t _ ↦ hterm t
    _ = 2 * (harmonic (r + 1) : ℝ) := by
      rw [Finset.sum_add_distrib]
      have hfirst : (∑ t : Fin (r+1), (((t : ℕ) + 1 : ℝ)⁻¹)) =
          (harmonic (r + 1) : ℝ) := by
        have hfin : (∑ t : Fin (r+1), (((t : ℕ) + 1 : ℝ)⁻¹)) =
            ∑ i ∈ Finset.range (r + 1), ((i + 1 : ℕ) : ℝ)⁻¹ := by
          convert
            (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ ((i + 1 : ℕ) : ℝ)⁻¹) (r + 1)) using 1 <;>
            norm_num
        rw [hfin]
        simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      have hsecond : (∑ t : Fin (r+1), (r - (t : ℕ) + 1 : ℝ)⁻¹) =
          ∑ t : Fin (r+1), (((t : ℕ) + 1 : ℝ)⁻¹) := by
        rw [← Equiv.sum_comp Fin.revPerm]
        apply Finset.sum_congr rfl
        intro t _
        simp [Fin.revPerm, Fin.rev, Nat.cast_sub (Nat.le_of_lt_succ t.isLt)]
      rw [hfirst, hsecond, hfirst]
      ring
    _ ≤ 2 * (1 + Real.log (r + 1 : ℕ)) := by
      gcongr
      exact harmonic_le_one_add_log (r + 1)
    _ ≤ 6 * Real.log r := by
      have hcast : (r + 1 : ℝ) ≤ 2 * r := by
        exact_mod_cast (show r + 1 ≤ 2 * r by omega)
      have hlogmono : Real.log (r + 1 : ℝ) ≤ Real.log (2 * r) :=
        Real.strictMonoOn_log.monotoneOn
          (show (0 : ℝ) < r + 1 by positivity) (mul_pos (by norm_num) hr0) hcast
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr0.ne'] at hlogmono
      have hlog2 : Real.log (2 : ℝ) ≤ Real.log r := by
        apply Real.strictMonoOn_log.monotoneOn (by norm_num) hr0
        norm_num
        exact_mod_cast (show 2 ≤ r by omega)
      norm_num [Nat.cast_add] at hlogmono ⊢
      linarith
