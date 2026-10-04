-- Prove2me | solution 1 for PiIrrationality.campaign_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-03T23:13:29.738634+00:00
-- url     : https://prove2.me/submissions/98a199c4-9aa1-42cf-9aa7-6b9a2fc0b4ea

import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Algebra.Order.Field.Basic
import Theorems.Thm_PiIrrationality_chudnovsky_bound

theorem solution : PiIrrationality.UpperBound (41 : ℝ) := by
  intro ε hε
  rcases PiIrrationality.chudnovsky_bound ε hε with ⟨Q, hQ⟩
  refine ⟨Q, ?_⟩
  intro p q hq hQle
  have hlt := hQ p q hq hQle
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq))
  have hexp : (19.8899945 : ℝ) + ε ≤ 41 + ε := by norm_num
  have hpow : (q : ℝ) ^ ((19.8899945 : ℝ) + ε) ≤ (q : ℝ) ^ ((41 : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hq1 hexp
  have hpos : 0 < (q : ℝ) ^ ((19.8899945 : ℝ) + ε) := Real.rpow_pos_of_pos hq0 _
  have hineq' : 1 / (q : ℝ) ^ ((41 : ℝ) + ε) ≤ 1 / (q : ℝ) ^ ((19.8899945 : ℝ) + ε) :=
    one_div_le_one_div_of_le hpos hpow
  exact lt_of_le_of_lt hineq' hlt
