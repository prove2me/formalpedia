-- Prove2me | solution 1 for ThreeSum.PrimeDensity.lowerScaled_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:57.805637+00:00
-- url     : https://prove2.me/submissions/f19a4c1c-bc3a-4cc8-9829-d03fa337b490

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Theorems.Thm_ThreeSum_Asymptotics_log_nat_tendsto_atTop
import Theorems.Thm_ThreeSum_BinomialEntropy_logarithmic_error_tendsto_zero


set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section
namespace ThreeSum.PrimeDensity
theorem _root_.solution : Tendsto lowerScaled atTop (𝓝 (4 * Real.log 2)) := by
  have herr := ThreeSum.BinomialEntropy.logarithmic_error_tendsto_zero (c := 4) (by norm_num)
  have hinv := ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop
  have hnum := (tendsto_const_nhds (x := 4 * Real.log 2)).sub herr
  have hsmall := hinv.const_mul (Real.log 4)
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
  have h := hnum.div hden (by norm_num : (1 + Real.log 4 * 0 : ℝ) ≠ 0)
  unfold lowerScaled
  simpa [Pi.div_def, Pi.mul_def, div_eq_mul_inv, Pi.inv_apply] using h
end ThreeSum.PrimeDensity
