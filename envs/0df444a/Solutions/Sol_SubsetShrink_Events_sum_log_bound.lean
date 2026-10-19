-- Prove2me | solution 1 for SubsetShrink.Events.sum_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T20:25:13.707652+00:00
-- url     : https://prove2.me/submissions/19187101-0e8d-409a-9bae-cfd4d51d7f77

/-
  DS7 target: SubsetShrink.Events.sum_log_bound
  theorem_id e4bc9c9a-3131-429d-ba34-413b27ca2aa2 (Open milestone of mission
  b3f99725-2ef4-482e-8cc0-ff264fd019ff).

  Feeds prob_F / eq_28: the exact finite-sum identity and its Stirling bound.
-/
import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem solution {p s : ℕ} (hs : 1 ≤ s) (hsp : s ≤ p) :
    ∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j) =
        (s : ℝ) * Real.log (2 * p) - Real.log (s.factorial) ∧
      ∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j) ≤
        (s : ℝ) * Real.log (2 * Real.exp 1 * p / s) := by
  have hp : (0 : ℕ) < p := lt_of_lt_of_le (by norm_num) (le_trans hs hsp)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hs)
  -- product identity ∏_{j∈Icc 1 s} j = s!
  have hprodN : (∏ j ∈ Finset.Icc 1 s, j) = s.factorial := by
    rw [← Finset.Ico_add_one_right_eq_Icc 1 s]
    exact Finset.prod_Ico_id_eq_factorial s
  have hprodR : (∏ j ∈ Finset.Icc 1 s, (j : ℝ)) = (s.factorial : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) hprodN
    simpa using this
  -- the log of the product is the sum of logs
  have hlogfact : ∑ j ∈ Finset.Icc 1 s, Real.log (j : ℝ) = Real.log (s.factorial) := by
    rw [← hprodR, Real.log_prod]
    intro j hj
    have h1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp h1 : j ≠ 0)
  -- termwise log(2p/j) = log(2p) - log j
  have hterm : ∀ j ∈ Finset.Icc 1 s,
      Real.log (2 * (p : ℝ) / (j : ℝ)) = Real.log (2 * (p : ℝ)) - Real.log (j : ℝ) := by
    intro j hj
    have hj0 : (j : ℝ) ≠ 0 := by
      have h1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp h1 : j ≠ 0)
    rw [Real.log_div (by positivity) hj0]
  have hpart1 : ∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j) =
      (s : ℝ) * Real.log (2 * p) - Real.log (s.factorial) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hlogfact, Finset.sum_const]
    rw [Nat.card_Icc]
    simp only [nsmul_eq_mul]
    have : (s + 1 - 1 : ℕ) = s := by omega
    rw [this]
  refine ⟨hpart1, ?_⟩
  -- Stirling lower bound: s log s - s ≤ log s!
  have hstir : (s : ℝ) * Real.log (s : ℝ) - (s : ℝ) ≤ Real.log (s.factorial) := by
    have h1 := Stirling.le_log_factorial_stirling (n := s) (by omega)
    have hlognn : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg (by exact_mod_cast hs)
    have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have hnonneg : 0 ≤ Real.log (s : ℝ) / 2 + Real.log (2 * Real.pi) / 2 :=
      add_nonneg (div_nonneg hlognn (by norm_num)) (div_nonneg hlog2pi (by norm_num))
    linarith
  calc ∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j)
      = (s : ℝ) * Real.log (2 * p) - Real.log (s.factorial) := hpart1
    _ ≤ (s : ℝ) * Real.log (2 * p) - ((s : ℝ) * Real.log (s : ℝ) - (s : ℝ)) := by
        linarith
    _ = (s : ℝ) * Real.log (2 * Real.exp 1 * p / s) := by
        have hlog : Real.log (2 * Real.exp 1 * p / s)
            = Real.log 2 + 1 + Real.log (p : ℝ) - Real.log (s : ℝ) := by
          rw [Real.log_div (by positivity) hsR.ne']
          rw [Real.log_mul (by positivity) hpR.ne']
          rw [Real.log_mul (by norm_num) (Real.exp_ne_zero 1)]
          rw [Real.log_exp]
        have hlog2p : Real.log (2 * (p : ℝ)) = Real.log 2 + Real.log (p : ℝ) :=
          Real.log_mul (by norm_num) hpR.ne'
        rw [hlog, hlog2p]
        ring
