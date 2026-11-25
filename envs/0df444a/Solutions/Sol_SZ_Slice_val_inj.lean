-- Prove2me | solution 1 for SZ.Slice.val_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:05.198897+00:00
-- url     : https://prove2.me/submissions/b9887598-8f79-433c-9552-814387e9c418

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_irrational_sq

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution {p q p' q' : ℤ}
    (h : (p : ℝ) + (q : ℝ) * S.sq = (p' : ℝ) + (q' : ℝ) * S.sq) : p = p' ∧ q = q' := by
  have hq : q = q' := by
    by_contra hne
    have hd : (q - q' : ℤ) ≠ 0 := sub_ne_zero.mpr hne
    have he : ((q - q' : ℤ) : ℝ) * S.sq = ((p' - p : ℤ) : ℝ) := by push_cast; linarith
    exact (S.irrational_sq.intCast_mul hd).ne_int (p' - p) he
  refine ⟨?_, hq⟩
  subst hq
  have : (p : ℝ) = (p' : ℝ) := by linarith
  exact_mod_cast this
end SZ.Slice
