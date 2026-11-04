-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.logarithmic_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:36.934354+00:00
-- url     : https://prove2.me/submissions/af9b439b-f1cd-4a87-a49d-c1f257bb57af

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {c : ℕ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => Real.log (c * m + 1 : ℝ) / m) atTop (𝓝 0) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hn : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun m : ℕ => (c : ℝ) * m + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (hn.const_mul_atTop hc')
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp harg
  have hi := hn.inv_tendsto_atTop
  have hprod := hl.mul ((tendsto_const_nhds (x := (c : ℝ))).add hi)
  have heq : (fun m : ℕ => Real.log (c * m + 1 : ℝ) / m) =ᶠ[atTop]
      (fun m : ℕ => (Real.log (c * m + 1 : ℝ) / (c * m + 1)) * ((c : ℝ) + (m : ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hm)
    field_simp
  apply Tendsto.congr' heq.symm
  simpa only [Function.comp_apply, id_eq, zero_mul, Pi.inv_apply] using hprod
end ThreeSum.BinomialEntropy
