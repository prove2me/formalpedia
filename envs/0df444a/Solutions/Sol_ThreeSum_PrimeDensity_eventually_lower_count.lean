-- Prove2me | solution 1 for ThreeSum.PrimeDensity.eventually_lower_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:13.689194+00:00
-- url     : https://prove2.me/submissions/3703f76c-74af-49e2-adad-bec175838b78

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Theorems.Thm_ThreeSum_PrimeDensity_lowerScaled_tendsto
import Theorems.Thm_ThreeSum_PrimeDensity_lowerScaled_identity
import Theorems.Thm_ThreeSum_Parameters_log_two_lower


set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section
namespace ThreeSum.PrimeDensity
theorem _root_.solution :
    ∀ᶠ y : ℕ in atTop, (2 : ℝ) * ((y : ℝ) / Real.log y) ≤ Nat.primeCounting (4 * y) := by
  have htwo : (2 : ℝ) < 4 * Real.log 2 := by linarith [ThreeSum.Parameters.log_two_lower]
  have hs := lowerScaled_tendsto.eventually (lt_mem_nhds htwo)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with y hs hy
  have hy1 : 1 < y := by omega
  have hratio : 0 ≤ (y : ℝ) / Real.log y := by
    apply div_nonneg (Nat.cast_nonneg y)
    exact (Real.log_pos (by exact_mod_cast hy1)).le
  have hmul := mul_le_mul_of_nonneg_right hs.le hratio
  rw [lowerScaled_identity hy1] at hmul
  have hpi := Chebyshev.pi_ge (4 * y)
  push_cast at hpi
  exact hmul.trans hpi
end ThreeSum.PrimeDensity
