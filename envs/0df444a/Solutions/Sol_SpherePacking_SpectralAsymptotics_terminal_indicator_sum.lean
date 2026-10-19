-- Prove2me | solution 1 for SpherePacking.SpectralAsymptotics.terminal_indicator_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/bfdf2d1e-205a-4ac8-a3e2-9f03d7d320a4

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
open Filter Topology
open scoped BigOperators Topology InnerProductSpace
open SpherePacking.SpectralAsymptotics
open SpherePacking.NumericalCertificate
namespace SpherePacking.SpectralAsymptotics
theorem _root_.solution (d m : ℕ) (hm : m ≤ d) :
    (∑ p ∈ Finset.range (d + 1), terminalIndicator d m p) =
      (m : ℝ) + 1 := by
  have hsplit : d + 1 = (d - m) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ p ∈ Finset.range (d - m), terminalIndicator d m p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp [terminalIndicator, Nat.not_le.mpr hp']
  rw [hfirst, zero_add]
  calc
    (∑ p ∈ Finset.range (m + 1),
      terminalIndicator d m (d - m + p)) =
        ∑ _p ∈ Finset.range (m + 1), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [terminalIndicator]
    _ = (m : ℝ) + 1 := by simp
end SpherePacking.SpectralAsymptotics
