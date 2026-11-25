-- Prove2me | solution 1 for SZ.pick_eq_02
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:36:45.838801+00:00
-- url     : https://prove2.me/submissions/444439d0-3c09-4f1e-ad8d-336a67ab5caa

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
section
namespace SZ
open Filter Topology
private theorem t3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {w : ℝ} (h1 : 2 * Real.sqrt 3 ≤ w) (h2 : w ≤ 1 + 3 * Real.sqrt 3) :
    pick w = (0, 2) := by
  have hne : ¬ (w ≤ 1 + Real.sqrt 3) := by intro hx; linarith [t3_lb]
  unfold pick
  rw [if_neg hne, if_neg (not_lt.mpr h1), if_pos h2]
end SZ
