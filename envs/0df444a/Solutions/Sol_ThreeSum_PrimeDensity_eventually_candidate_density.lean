-- Prove2me | solution 1 for ThreeSum.PrimeDensity.eventually_candidate_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:47.704103+00:00
-- url     : https://prove2.me/submissions/49e4c908-5875-4be9-989d-f171f5344eda

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Theorems.Thm_ThreeSum_PrimeDensity_candidate_card_add
import Theorems.Thm_ThreeSum_PrimeDensity_eventually_lower_count
import Theorems.Thm_ThreeSum_PrimeDensity_eventually_upper_count

set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section
namespace ThreeSum.PrimeDensity
theorem _root_.solution :
    ∀ᶠ y : ℕ in atTop, (y : ℝ) / (4 * Real.log y) ≤ ((candidates y).card : ℝ) := by
  filter_upwards [eventually_lower_count, eventually_upper_count] with y hlo hhi
  have hcard : ((candidates y).card : ℝ) + (Nat.primeCounting y : ℝ) =
      (Nat.primeCounting (4 * y) : ℝ) := by exact_mod_cast candidate_card_add y
  have hid : (y : ℝ) / (4 * Real.log y) = (1 / 4 : ℝ) * ((y : ℝ) / Real.log y) := by ring
  rw [hid]
  linarith
end ThreeSum.PrimeDensity
