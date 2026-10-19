-- Prove2me | solution 1 for SpherePacking.SpectralAsymptotics.terminal_edge_sum_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/4ad4e599-4da7-472a-908c-cbc9b424ccae

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminalVector_ne_zero
import Theorems.Thm_MetricCodes_Hamming_terminalVector_rayleigh
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_ne_zero
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_rayleigh
import Theorems.Thm_SpherePacking_SpectralAsymptotics_terminalVector_ne_zero
import Theorems.Thm_SpherePacking_SpectralAsymptotics_terminalVector_rayleigh

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
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    (2 * ∑ r ∈ Finset.range m,
      Gegenbauer.jacobiCoefficient n k (L - m + r)) /
        ((m : ℝ) + 1) ≤
      Jacobi.topEigenvalue n k L := by
  rw [← terminalVector_rayleigh n k L m hkl hm]
  exact Jacobi.rayleigh_le_top n k L
    (terminalVector k L m) (terminalVector_ne_zero k L m)
end SpherePacking.SpectralAsymptotics
