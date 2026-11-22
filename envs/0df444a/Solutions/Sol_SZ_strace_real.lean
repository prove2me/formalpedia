-- Prove2me | solution 1 for SZ.strace_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:21.419414+00:00
-- url     : https://prove2.me/submissions/379e123f-ec65-477b-b82e-861bb1edd72f

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_QuadThm6
import Theorems.Thm_SZ_sqrtThree_pair
import Theorems.Thm_SZ_Pair_sq_alpha
import Theorems.Thm_SZ_Pair_sq_beta
import Theorems.Thm_SZ_rec2_one
import Theorems.Thm_SZ_rec2_real
import Theorems.Thm_SZ_rec2_zero
attribute [local simp] SZ.rec2_one
attribute [local simp] SZ.rec2_zero



set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) :
    (1 + Real.sqrt 3) ^ n + (1 - Real.sqrt 3) ^ n = (rec2 2 2 2 2 n : ℝ) := by
  have h := rec2_real (A := 2) (B := 2) (t₀ := 2) (t₁ := 2) (u := (1 : ℝ)) (v := (1 : ℝ))
    sqrtThree_pair.sq_alpha sqrtThree_pair.sq_beta (by norm_num) (by push_cast; ring) n
  simpa using h
end SZ
