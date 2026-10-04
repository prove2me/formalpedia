-- Prove2me | solution 1 for PiIrrationality.campaign_bound_206
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-03T23:13:30.649521+00:00
-- url     : https://prove2.me/submissions/129a3d48-d9b1-4e36-998f-48369898c3da

import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Algebra.Order.Field.Basic
import Theorems.Thm_PiIrrationality_chudnovsky_bound

theorem solution : PiIrrationality.UpperBound (20.6 : ℝ) := by
  intro ε hε
  rcases PiIrrationality.chudnovsky_bound ε hε with ⟨Q, hQ⟩
  refine ⟨Q, ?_⟩
  intro p q hq hQle
  have hlt := hQ p q hq hQle
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq))
  have hexp : (19.8899945 : ℝ) + ε ≤ 20.6 + ε := by norm_num
  have hpow : (q : ℝ) ^ ((19.8899945 : ℝ) + ε) ≤ (q : ℝ) ^ ((20.6 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hq1 hexp
  have hpos : 0 < (q : ℝ) ^ ((19.8899945 : ℝ) + ε) := Real.rpow_pos_of_pos hq0 _
  have hineq' : 1 / (q : ℝ) ^ ((20.6 : ℝ) + ε) ≤ 1 / (q : ℝ) ^ ((19.8899945 : ℝ) + ε) :=
    one_div_le_one_div_of_le hpos hpow
  exact lt_of_le_of_lt hineq' hlt
