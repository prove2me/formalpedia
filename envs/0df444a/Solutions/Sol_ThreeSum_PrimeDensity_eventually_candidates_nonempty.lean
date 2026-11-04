-- Prove2me | solution 1 for ThreeSum.PrimeDensity.eventually_candidates_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:43.611682+00:00
-- url     : https://prove2.me/submissions/fc75047a-cd80-442b-a6a5-56d2c7fd7216

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Theorems.Thm_ThreeSum_PrimeDensity_eventually_candidate_density

set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section
namespace ThreeSum.PrimeDensity
theorem _root_.solution :
    ∀ᶠ y : ℕ in atTop, (candidates y).Nonempty := by
  filter_upwards [eventually_candidate_density, eventually_ge_atTop (2 : ℕ)] with y hy hge
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hpos : (0 : ℝ) < (y : ℝ) / (4 * Real.log y) := by
    apply div_pos (by linarith)
    exact mul_pos (by norm_num) (Real.log_pos hy1)
  apply card_pos.mp
  exact_mod_cast lt_of_lt_of_le hpos hy
end ThreeSum.PrimeDensity
