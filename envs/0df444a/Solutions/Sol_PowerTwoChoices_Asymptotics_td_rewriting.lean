-- Prove2me | solution 1 for PowerTwoChoices.Asymptotics.td_rewriting
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:02:46.856113+00:00
-- url     : https://prove2.me/submissions/347a0646-f19e-49d3-b924-3b79072d3159

import Mathlib
import Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime

set_option autoImplicit false
open Filter Topology

theorem solution (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    Summable (fun i : ℕ => if 1 ≤ i then (lam ^ (1 / ((d : ℝ) - 1))) ^ (d ^ i) else 0) ∧
      PowerTwoChoices.Asymptotics.Td d lam =
        (∑' i : ℕ, if 1 ≤ i then (lam ^ (1 / ((d : ℝ) - 1))) ^ (d ^ i) else 0) /
          lam ^ ((d : ℝ) / ((d : ℝ) - 1)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  set q : ℝ := 1 / ((d : ℝ) - 1) with hq
  have hqpos : 0 < q := by positivity
  have hlq0 : 0 ≤ lam ^ q := Real.rpow_nonneg h0.le _
  have hlq1 : lam ^ q < 1 := Real.rpow_lt_one h0.le h1 hqpos
  -- geometric sum identity
  have hgeo : ∀ i : ℕ, 1 ≤ i →
      ((∑ k ∈ Finset.Ico 1 i, d ^ k : ℕ) : ℝ) * ((d : ℝ) - 1) = (d : ℝ) ^ i - d := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => simp
    | succ i hi ih =>
      rw [Finset.sum_Ico_succ_top hi]
      push_cast at ih ⊢
      rw [add_mul, ih]
      ring
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      (summable_geometric_of_lt_one hlq0 hlq1)
    · split_ifs
      · exact pow_nonneg hlq0 _
      · exact le_rfl
    · split_ifs with hi
      · exact pow_le_pow_of_le_one hlq0 hlq1.le (Nat.lt_pow_self (by omega)).le
      · exact pow_nonneg hlq0 _
  · have hpt : ∀ i : ℕ, (if 1 ≤ i then lam ^ (∑ k ∈ Finset.Ico 1 i, d ^ k) else 0) =
        (if 1 ≤ i then (lam ^ q) ^ (d ^ i) else 0) / lam ^ ((d : ℝ) / ((d : ℝ) - 1)) := by
      intro i
      by_cases hi : 1 ≤ i
      · simp only [hi, if_true]
        have hN : ((∑ k ∈ Finset.Ico 1 i, d ^ k : ℕ) : ℝ) = q * ((d : ℝ) ^ i - d) := by
          rw [← hgeo i hi, hq]
          field_simp
        have e1 : (lam ^ q) ^ (d ^ i) = lam ^ (q * (d : ℝ) ^ i) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]
          push_cast; rfl
        have e2 : (d : ℝ) / ((d : ℝ) - 1) = q * d := by rw [hq]; ring
        rw [e1, e2, eq_div_iff (Real.rpow_pos_of_pos h0 _).ne', ← Real.rpow_natCast, hN,
          ← Real.rpow_add h0]
        congr 1
        ring
      · simp [hi]
    unfold PowerTwoChoices.Asymptotics.Td
    rw [tsum_congr hpt, tsum_div_const]
