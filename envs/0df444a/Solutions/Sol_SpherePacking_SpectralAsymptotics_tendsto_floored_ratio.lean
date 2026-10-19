-- Prove2me | solution 1 for SpherePacking.SpectralAsymptotics.tendsto_floored_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/59958fc8-d62f-49db-bd63-0e3c50897fe7

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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌊a * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa [Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
end SpherePacking.SpectralAsymptotics
