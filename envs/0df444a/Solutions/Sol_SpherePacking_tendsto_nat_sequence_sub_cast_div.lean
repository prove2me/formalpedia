-- Prove2me | solution 1 for SpherePacking.tendsto_nat_sequence_sub_cast_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/3790120c-5a81-4738-859e-7300cbc0f6cf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (N : ℕ → ℕ) (c : ℕ) (u : ℝ)
    (hN : Tendsto N atTop atTop)
    (hNu : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds u)) :
    Tendsto (fun n : ℕ => ((N n - c : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds u) := by
  have hsub := hNu.sub (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  have heq :
      (fun n : ℕ => (N n : ℝ) / (n : ℝ) - (c : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => ((N n - c : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [hN.eventually (eventually_ge_atTop c)] with n hn
    rw [Nat.cast_sub hn, sub_div]
  simpa using hsub.congr' heq
end SpherePacking
