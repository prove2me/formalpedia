-- Prove2me | solution 1 for PropagatorLimit.Scaling.explicit_solution
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:22:29.499375+00:00
-- url     : https://prove2.me/submissions/02bef6e4-7510-45cb-9312-916e251e774f

import Mathlib
import Definitions.Def_PropagatorLimit_Scaling_Model

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

open PropagatorLimit.Scaling in
theorem solution {Ω : Type} (beta : ℝ) (T : ℝ≥0) (g : ℝ → ℝ) (F : ℝ≥0 → Ω → ℝ)
    (N n : ℕ) (ω : Ω) :
    INdisc beta T g F N n ω =
        ∑ m ∈ Finset.Icc 1 n, (1 - beta * dt T N) ^ (n - m) *
          (Real.sqrt (dt T N) * g (incr T N F m ω / Real.sqrt (dt T N))) ∧
      (beta * dt T N ≠ 1 →
        INdisc beta T g F N n ω =
          (1 - beta * dt T N) ^ n * Real.sqrt (dt T N) *
            ∑ m ∈ Finset.Icc 1 n, (1 - beta * dt T N) ^ (-(m : ℤ)) *
              g (incr T N F m ω / Real.sqrt (dt T N))) := by
  set a := 1 - beta * dt T N with ha
  set c : ℕ → ℝ := fun m => Real.sqrt (dt T N) * g (incr T N F m ω / Real.sqrt (dt T N)) with hc
  have part1 : ∀ n : ℕ, INdisc beta T g F N n ω = ∑ m ∈ Finset.Icc 1 n, a ^ (n - m) * c m := by
    intro n
    induction n with
    | zero => simp [INdisc]
    | succ n ih =>
      have hstep : INdisc beta T g F N (n + 1) ω = a * INdisc beta T g F N n ω + c (n + 1) := by
        show INdisc beta T g F N n ω - beta * INdisc beta T g F N n ω * dt T N +
          gN T N g (incr T N F (n + 1) ω) = _
        rw [ha, hc]; unfold gN; ring
      rw [hstep, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.mul_sum,
        Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
      rw [show n + 1 - m = (n - m) + 1 by omega, pow_succ]
      ring
  refine ⟨part1 n, ?_⟩
  intro hne
  have ha0 : a ≠ 0 := by rw [ha]; intro h; apply hne; linarith
  rw [part1 n, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
  have hz : a ^ (n - m) = a ^ n * a ^ (-(m : ℤ)) := by
    rw [← zpow_natCast, Nat.cast_sub hmn, sub_eq_add_neg, zpow_add₀ ha0, zpow_natCast]
  rw [hz, hc]
  ring
