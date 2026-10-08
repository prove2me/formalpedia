-- Prove2me | solution 1 for WeightedRootIntegralIdentity.contour_boundary_from_limit_components
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T13:56:13.540029+00:00
-- url     : https://prove2.me/submissions/41c6582d-76fd-4168-a4bc-289c2efcc8b9

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_contour_limit_assembly
theorem solution (Iupper Ilower Iinner Iouter residue Ibank : ℂ) (hbank : Iupper + Ilower = 2 * Ibank) (harcs : Iinner + Iouter = 0) (hboundary : Iupper + Ilower + Iinner + Iouter = 2 * Real.pi * Complex.I * residue) : 2 * Ibank = 2 * Real.pi * Complex.I * residue := by
  exact WeightedRootIntegralIdentity.contour_limit_assembly Iupper Ilower Iinner Iouter residue Ibank hbank harcs hboundary
