-- Prove2me | solution 1 for SpherePacking.tendsto_log_harmonicDimension_div_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/d3dfee9d-29ca-4dca-819d-03467e57699d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_harmonicDimension_div

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
        (Real.log
          (Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ : ℝ) /
          (n : ℝ)) / Real.log 2)
      atTop (nhds (NumericalCertificate.binaryEntropy u)) := by
  simpa [NumericalCertificate.binaryEntropy] using
    (tendsto_log_harmonicDimension_div u hu N hN hNratio).div_const
      (Real.log 2)
end SpherePacking
