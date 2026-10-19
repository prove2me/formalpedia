-- Prove2me | solution 1 for SpherePacking.SpectralAsymptotics.terminalVector_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/84108ccb-8359-46a4-a4ef-60e46da23207

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminalVector_norm_sq
import Theorems.Thm_MetricCodes_Hamming_terminalVector_inner
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_norm_sq
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_inner
import Theorems.Thm_SpherePacking_SpectralAsymptotics_terminalVector_norm_sq
import Theorems.Thm_SpherePacking_SpectralAsymptotics_terminalVector_inner

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
    Jacobi.rayleigh n k L (terminalVector k L m) =
      (2 * ∑ r ∈ Finset.range m,
        Gegenbauer.jacobiCoefficient n k (L - m + r)) /
          ((m : ℝ) + 1) := by
  rw [Jacobi.rayleigh_eq_inner,
    terminalVector_inner n k L m hkl hm,
    terminalVector_norm_sq k L m hm]
end SpherePacking.SpectralAsymptotics
