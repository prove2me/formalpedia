-- Prove2me | solution 1 for WeightedRootIntegralIdentity.contour_limit_assembly
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T13:49:20.406695+00:00
-- url     : https://prove2.me/submissions/dfc1de3f-4a35-4e80-bdee-fbd620d95359

import Mathlib
theorem solution (Iupper Ilower Iinner Iouter residue Ibank : ℂ) (hbank : Iupper + Ilower = 2 * Ibank) (harcs : Iinner + Iouter = 0) (hboundary : Iupper + Ilower + Iinner + Iouter = 2 * Real.pi * Complex.I * residue) : 2 * Ibank = 2 * Real.pi * Complex.I * residue := by
  have htotal : 2 * Ibank = Iupper + Ilower + Iinner + Iouter := by
    calc
      2 * Ibank = Iupper + Ilower := hbank.symm
      _ = (Iupper + Ilower) + (Iinner + Iouter) := by rw [harcs]; ring
      _ = Iupper + Ilower + Iinner + Iouter := by ring
  exact htotal.trans hboundary
