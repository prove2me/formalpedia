-- Prove2me | solution 1 for SpherePacking.tendsto_log_harmonicDimensionQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/930422d9-919e-4d59-8bd9-33da5e3fc7d6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_harmonicDimension_div_log_two
import Theorems.Thm_SpherePacking_tendsto_nat_succ_cast_div
import Theorems.Thm_SpherePacking_tendsto_nat_pred_cast_div

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped BigOperators Nat Topology
namespace SpherePacking
theorem _root_.solution
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (harmonicDimensionQuotient a b n) / (n : ℝ)) /
          Real.log 2)
      atTop
      (nhds (NumericalCertificate.binaryEntropy a -
        NumericalCertificate.binaryEntropy b)) := by
  have hnum := tendsto_log_harmonicDimension_div_log_two
    a ha (fun n : ℕ => n + 1)
    (tendsto_add_atTop_nat 1) tendsto_nat_succ_cast_div
  have hden := tendsto_log_harmonicDimension_div_log_two
    b hb (fun n : ℕ => n - 1)
    (tendsto_sub_atTop_nat 1) tendsto_nat_pred_cast_div
  have hdiff := hnum.sub hden
  have heq :
      (fun n : ℕ =>
        (Real.log
          (Gegenbauer.harmonicDimension (n + 1) ⌊a * (n : ℝ)⌋₊ : ℝ) /
          (n : ℝ)) / Real.log 2 -
        (Real.log
          (Gegenbauer.harmonicDimension (n - 1) ⌊b * (n : ℝ)⌋₊ : ℝ) /
          (n : ℝ)) / Real.log 2) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.log (harmonicDimensionQuotient a b n) / (n : ℝ)) /
          Real.log 2) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnumpos :
        0 <
          (Gegenbauer.harmonicDimension
            (n + 1) ⌊a * (n : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast
        Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n + 1)
          ⌊a * (n : ℝ)⌋₊
    have hdenpos :
        0 <
          (Gegenbauer.harmonicDimension
            (n - 1) ⌊b * (n : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast
        Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n - 1)
          ⌊b * (n : ℝ)⌋₊
    unfold harmonicDimensionQuotient
    rw [Real.log_div hnumpos.ne' hdenpos.ne']
    ring
  exact hdiff.congr' heq
end SpherePacking
