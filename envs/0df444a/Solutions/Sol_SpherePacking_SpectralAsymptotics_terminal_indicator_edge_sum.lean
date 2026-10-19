-- Prove2me | solution 1 for SpherePacking.SpectralAsymptotics.terminal_indicator_edge_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/076a9c06-8109-4735-a2db-d14e33ced4fb

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
theorem _root_.solution
    (d m : ℕ) (hm : m ≤ d) (c : ℕ → ℝ) :
    (∑ p ∈ Finset.range d,
      c p * terminalIndicator d m p *
        terminalIndicator d m (p + 1)) =
      ∑ r ∈ Finset.range m, c (d - m + r) := by
  have hsplit : d = (d - m) + m := by omega
  rw [hsplit, Finset.sum_range_add]
  simp only [← hsplit]
  have hfirst :
      (∑ p ∈ Finset.range (d - m),
        c p * terminalIndicator d m p *
          terminalIndicator d m (p + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp [terminalIndicator, Nat.not_le.mpr hp']
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ : d - m ≤ d - m + p := by omega
  have h₂ : d - m ≤ d - m + p + 1 := by omega
  simp only [terminalIndicator, if_pos h₁, if_pos h₂, mul_one]
end SpherePacking.SpectralAsymptotics
