-- Prove2me | solution 1 for SpherePacking.SpectralAsymptotics.jacobiCoefficient_eq_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/96fd2560-16a5-43f1-9f05-7b6e8ebdc7b3

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
    (n k i : ℕ) (hn : 0 < n) :
    Gegenbauer.jacobiCoefficient n k i =
      normalizedCoefficient
        ((i : ℝ) / (n : ℝ))
        ((k : ℝ) / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnreal
  unfold Gegenbauer.jacobiCoefficient normalizedCoefficient
  have hrad :
      (((i : ℝ) + 1) * ((i : ℝ) + (n : ℝ) - 2) *
        (2 * (i : ℝ) + (n : ℝ) - 2) *
        (2 * (i : ℝ) + (n : ℝ))) =
      (((n : ℝ) ^ 2) ^ 2) *
        (((i : ℝ) / n + (1 : ℝ) / n) *
          ((i : ℝ) / n + 1 - 2 * ((1 : ℝ) / n)) *
          (2 * ((i : ℝ) / n) + 1 - 2 * ((1 : ℝ) / n)) *
          (2 * ((i : ℝ) / n) + 1)) := by
    field_simp [hnne]
  rw [hrad, Real.sqrt_mul (sq_nonneg ((n : ℝ) ^ 2)),
    Real.sqrt_sq (sq_nonneg (n : ℝ)), div_mul_eq_div_div]
  congr 1
  field_simp [hnne]
end SpherePacking.SpectralAsymptotics
