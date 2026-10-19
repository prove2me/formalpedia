-- Prove2me | solution 1 for SpherePacking.tendsto_log_const_mul_harmonicDimensionQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/3f23b8c8-f253-48a0-a2a2-ed5f305c1588

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_harmonicDimensionQuotient_pos
import Theorems.Thm_SpherePacking_tendsto_log_harmonicDimensionQuotient

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
    (a b C : ℝ) (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (C * harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2)
      atTop
      (nhds (NumericalCertificate.binaryEntropy a -
        NumericalCertificate.binaryEntropy b)) := by
  have hquot := tendsto_log_harmonicDimensionQuotient a b ha hb
  have hconstant :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).div_const
      (Real.log 2)
  have hsum := hconstant.add hquot
  have heq :
      (fun n : ℕ =>
        (Real.log C / (n : ℝ)) / Real.log 2 +
          (Real.log (harmonicDimensionQuotient a b n) /
            (n : ℝ)) / Real.log 2) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.log (C * harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    rw [Real.log_mul hC.ne'
      (harmonicDimensionQuotient_pos a b hn).ne']
    ring
  simpa using hsum.congr' heq
end SpherePacking
