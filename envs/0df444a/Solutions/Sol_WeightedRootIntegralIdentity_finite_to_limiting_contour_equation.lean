-- Prove2me | solution 1 for WeightedRootIntegralIdentity.finite_to_limiting_contour_equation
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T14:31:16.772113+00:00
-- url     : https://prove2.me/submissions/fdcc7656-ee25-46da-ae18-c38c74b69253

import Mathlib
theorem solution (Iupper Ilower Iinner Iouter U L residue : ℂ) (hupper : Iupper = U) (hlower : Ilower = L) (hinner : Iinner = 0) (houter : Iouter = 0) (hrect : U + L = 2 * Real.pi * Complex.I * residue) : Iupper + Ilower + Iinner + Iouter = 2 * Real.pi * Complex.I * residue := by
  rw [hupper, hlower, hinner, houter]
  simpa using hrect
