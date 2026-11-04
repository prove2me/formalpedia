-- Prove2me | solution 1 for ThreeSum.Asymptotics.natCost_isBigO_of_vanishing_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:55.55833+00:00
-- url     : https://prove2.me/submissions/6eaac15b-147f-42e2-b2ee-a1c590f844de

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Theorems.Thm_ThreeSum_Parameters_certificate_lt_target


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Asymptotics
open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.Asymptotics
theorem _root_.solution {T : ℕ → ℕ} {w : ℕ → ℝ}
    (hw : Tendsto w atTop (𝓝 0))
    (hcost : ∀ᶠ n : ℕ in atTop,
      (T n : ℝ) ≤ (n : ℝ) ^ (certificateExponent + w n)) :
    (fun n : ℕ => (T n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ targetExponent) := by
  have hgap : 0 < targetExponent - certificateExponent := sub_pos.mpr certificate_lt_target
  have hwsmall := hw.eventually (gt_mem_nhds hgap)
  apply Asymptotics.IsBigO.of_norm_eventuallyLE
  filter_upwards [hcost, hwsmall, eventually_ge_atTop (1 : ℕ)] with n hc hw hn
  have hle : (T n : ℝ) ≤ (n : ℝ) ^ targetExponent :=
    hc.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (T n : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ targetExponent)] using hle
end ThreeSum.Asymptotics
