-- Prove2me | solution 1 for ThreeSum.Asymptotics.overheadEnvelope_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:05.216721+00:00
-- url     : https://prove2.me/submissions/9d4b7414-0a09-4416-95c7-8bef61879589

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Theorems.Thm_ThreeSum_Asymptotics_overheadExponent_tendsto_zero

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Asymptotics
open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.Asymptotics
theorem _root_.solution {C d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, overheadEnvelope C n ≤ (n : ℝ) ^ d := by
  have ho := (overheadExponent_tendsto_zero C).eventually (gt_mem_nhds hd)
  filter_upwards [ho, eventually_ge_atTop (1 : ℕ)] with n hn hge
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hge) hn.le
end ThreeSum.Asymptotics
