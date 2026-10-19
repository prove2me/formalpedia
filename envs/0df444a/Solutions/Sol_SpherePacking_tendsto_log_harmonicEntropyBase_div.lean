-- Prove2me | solution 1 for SpherePacking.tendsto_log_harmonicEntropyBase_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/0fbe8a0e-bf1e-40e2-baf2-c4a1c60c5973

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_add_choose_div
import Theorems.Thm_SpherePacking_tendsto_nat_sequence_sub_cast_div

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
      (fun n : ℕ => Real.log (harmonicEntropyBase u N n : ℝ) / (n : ℝ))
      atTop (nhds ((1 + u) * Real.log (1 + u) - u * Real.log u)) := by
  have hfloor :
      Tendsto (fun n : ℕ => (⌊u * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
        atTop (nhds u) :=
    (tendsto_nat_floor_mul_div_atTop hu.le).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hambient : Tendsto (fun n : ℕ => N n - 2) atTop atTop :=
    (tendsto_sub_atTop_nat 2).comp hN
  have hambientratio :
      Tendsto (fun n : ℕ => ((N n - 2 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds 1) :=
    tendsto_nat_sequence_sub_cast_div N 2 1 hN hNratio
  have h := tendsto_log_add_choose_div
    (fun n : ℕ => ⌊u * (n : ℝ)⌋₊)
    (fun n : ℕ => N n - 2)
    u 1
    (tendsto_nat_floor_mul_atTop u hu)
    hambient
    hfloor hambientratio hu (by norm_num)
  simpa [harmonicEntropyBase, Real.log_one, add_comm] using h
end SpherePacking
