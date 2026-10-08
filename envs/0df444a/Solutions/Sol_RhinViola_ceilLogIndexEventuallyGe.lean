-- Prove2me | solution 1 for RhinViola.ceilLogIndexEventuallyGe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T14:23:27.540342+00:00
-- url     : https://prove2.me/submissions/bbcaeceb-9085-4fc7-8e08-3874fa6af2af

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem solution
    (u : ℝ) (N : ℕ) (hu : 0 < u) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
      N ≤ ⌈Real.log (2 * (q : ℝ)) / u⌉₊ := by
  let Q : ℕ := ⌈Real.exp (u * (N : ℝ))⌉₊
  refine ⟨Q, ?_⟩
  intro q hQq hq
  have hqR : 0 < (q : ℝ) := by
    exact_mod_cast hq
  have htwoq : 0 < (2 : ℝ) * (q : ℝ) := by
    positivity
  have hexp_le_Q :
      Real.exp (u * (N : ℝ)) ≤ (Q : ℝ) := by
    dsimp [Q]
    exact Nat.le_ceil _
  have hQ_le_q : (Q : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hQq
  have hq_le_twoq : (q : ℝ) ≤ 2 * (q : ℝ) := by
    nlinarith
  have hexp_le_twoq :
      Real.exp (u * (N : ℝ)) ≤ 2 * (q : ℝ) :=
    le_trans hexp_le_Q (le_trans hQ_le_q hq_le_twoq)
  have hlog :
      u * (N : ℝ) ≤ Real.log (2 * (q : ℝ)) :=
    (Real.le_log_iff_exp_le htwoq).2 hexp_le_twoq
  have hratio :
      (N : ℝ) ≤ Real.log (2 * (q : ℝ)) / u := by
    apply (le_div_iff₀ hu).2
    simpa [mul_comm] using hlog
  have hceil :
      Real.log (2 * (q : ℝ)) / u ≤
        (⌈Real.log (2 * (q : ℝ)) / u⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hcast :
      (N : ℝ) ≤
        (⌈Real.log (2 * (q : ℝ)) / u⌉₊ : ℝ) :=
    le_trans hratio hceil
  exact_mod_cast hcast
