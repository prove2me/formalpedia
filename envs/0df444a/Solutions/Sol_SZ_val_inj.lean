-- Prove2me | solution 1 for SZ.val_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:49.964874+00:00
-- url     : https://prove2.me/submissions/d5e12db1-dda0-4132-9ddc-e31d12ab941a

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_irrational_sqrt_three

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {p q p' q' : ℤ}
    (h : (p : ℝ) + (q : ℝ) * Real.sqrt 3 = (p' : ℝ) + (q' : ℝ) * Real.sqrt 3) :
    p = p' ∧ q = q' := by
  have hq : q = q' := by
    by_contra hne
    have hd : (q - q' : ℤ) ≠ 0 := sub_ne_zero.mpr hne
    have he : ((q - q' : ℤ) : ℝ) * Real.sqrt 3 = ((p' - p : ℤ) : ℝ) := by push_cast; linarith
    exact (irrational_sqrt_three.intCast_mul hd).ne_int (p' - p) he
  refine ⟨?_, hq⟩
  subst hq
  have : (p : ℝ) = (p' : ℝ) := by linarith
  exact_mod_cast this
end SZ
