-- Prove2me | solution 1 for SZ.pick_residual_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:08:02.90324+00:00
-- url     : https://prove2.me/submissions/210d7162-cfdd-449c-bca1-1b5b6e95fea1

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_pick_cases
section
namespace SZ
open Filter Topology
private theorem s3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
private theorem s3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 3 + 3 * Real.sqrt 3) :
    0 ≤ w - (((pick w).1 : ℝ) + ((pick w).2 : ℝ) * Real.sqrt 3) ∧
      w - (((pick w).1 : ℝ) + ((pick w).2 : ℝ) * Real.sqrt 3) ≤ 1 + Real.sqrt 3 := by
  rcases pick_cases w with ⟨hw, hp⟩ | ⟨ha, hb, hp⟩ | ⟨ha, hb, hp⟩ | ⟨hw, hp⟩ <;> rw [hp] <;>
    norm_num <;> constructor <;> linarith [s3_lb, s3_ub]
end SZ
