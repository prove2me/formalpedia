-- Prove2me | solution 1 for SpherePacking.tendsto_log_two_mul_harmonicEntropyBase_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/42fbaa5b-4066-4b8b-ae9c-7e8071111e20

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_harmonicEntropyBase_pos
import Theorems.Thm_SpherePacking_tendsto_log_harmonicEntropyBase_div

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
open scoped Nat Topology
namespace SpherePacking
theorem _root_.solution
    (u : ℝ) (hu : 0 < u)
    (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hNratio : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun n : ℕ =>
        Real.log ((2 * harmonicEntropyBase u N n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds ((1 + u) * Real.log (1 + u) - u * Real.log u)) := by
  have hbase := tendsto_log_harmonicEntropyBase_div u hu N hN hNratio
  have htwo := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hsum := htwo.add hbase
  have heq :
      (fun n : ℕ =>
        Real.log 2 / (n : ℝ) +
          Real.log (harmonicEntropyBase u N n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log ((2 * harmonicEntropyBase u N n : ℕ) : ℝ) / (n : ℝ)) := by
    apply Eventually.of_forall
    intro n
    change
      Real.log 2 / (n : ℝ) +
          Real.log (harmonicEntropyBase u N n : ℝ) / (n : ℝ) =
        Real.log ((2 * harmonicEntropyBase u N n : ℕ) : ℝ) / (n : ℝ)
    push_cast
    rw [Real.log_mul (by norm_num)
      (by exact_mod_cast (harmonicEntropyBase_pos u N n).ne')]
    rw [add_div]
  simpa using hsum.congr' heq
end SpherePacking
