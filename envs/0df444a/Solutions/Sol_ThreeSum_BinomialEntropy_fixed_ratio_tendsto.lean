-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.fixed_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:24.684188+00:00
-- url     : https://prove2.me/submissions/136a9f85-a099-47f8-93b7-1d49ad30bc65

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_bounds
import Theorems.Thm_ThreeSum_BinomialEntropy_logarithmic_error_tendsto_zero

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {c r : ℕ} (hc : 0 < c) (hr : r ≤ c) :
    Tendsto (fun m : ℕ => Real.log ((c * m).choose (r * m) : ℝ) / m) atTop
      (𝓝 ((c : ℝ) * Real.binEntropy ((r : ℝ) / c))) := by
  have herr := logarithmic_error_tendsto_zero hc
  have hlo := (tendsto_const_nhds (x := (c : ℝ) * Real.binEntropy ((r : ℝ) / c))).sub herr
  have hbounds : ∀ᶠ m : ℕ in atTop,
      (c : ℝ) * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) / m ≤
          Real.log ((c * m).choose (r * m) : ℝ) / m ∧
        Real.log ((c * m).choose (r * m) : ℝ) / m ≤
          (c : ℝ) * Real.binEntropy ((r : ℝ) / c) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact fixed_ratio_bounds hc hr (by omega)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hlo) tendsto_const_nhds (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
end ThreeSum.BinomialEntropy
