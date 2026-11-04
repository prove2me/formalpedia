-- Prove2me | solution 1 for ThreeSum.Asymptotics.natCost_isBigO_of_explicit_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:06.370009+00:00
-- url     : https://prove2.me/submissions/34db403f-8386-4c3c-ba9e-ca8f1c668aa4

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Theorems.Thm_ThreeSum_Asymptotics_overheadExponent_tendsto_zero
import Theorems.Thm_ThreeSum_Asymptotics_natCost_isBigO_of_vanishing_exponent

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Asymptotics
open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.Asymptotics
theorem _root_.solution {T : ℕ → ℕ} {C : ℝ}
    (hcost : ∀ᶠ n : ℕ in atTop,
      (T n : ℝ) ≤ (n : ℝ) ^ certificateExponent * overheadEnvelope C n) :
    (fun n : ℕ => (T n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ targetExponent) := by
  apply natCost_isBigO_of_vanishing_exponent (overheadExponent_tendsto_zero C)
  filter_upwards [hcost, eventually_ge_atTop (1 : ℕ)] with n hc hn
  rw [overheadEnvelope, ← Real.rpow_add (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn))] at hc
  exact hc
end ThreeSum.Asymptotics
