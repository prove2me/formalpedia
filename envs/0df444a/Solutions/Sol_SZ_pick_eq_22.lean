-- Prove2me | solution 1 for SZ.pick_eq_22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:35.229809+00:00
-- url     : https://prove2.me/submissions/fe539d7b-2077-4789-8e65-89558f7a8e10

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
section
namespace SZ
open Filter Topology
private theorem s3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {w : ℝ} (h : 1 + 3 * Real.sqrt 3 < w) : pick w = (2, 2) := by
  have hne1 : ¬ (w ≤ 1 + Real.sqrt 3) := by intro hx; linarith [s3_lb]
  have hne2 : ¬ (w < 2 * Real.sqrt 3) := by intro hx; linarith [s3_lb]
  unfold pick; rw [if_neg hne1, if_neg hne2, if_neg (not_le.mpr h)]
end SZ
