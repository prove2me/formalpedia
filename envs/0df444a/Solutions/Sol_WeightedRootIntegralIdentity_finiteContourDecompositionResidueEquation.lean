-- Prove2me | solution 1 for WeightedRootIntegralIdentity.finiteContourDecompositionResidueEquation
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:55:22.415735+00:00
-- url     : https://prove2.me/submissions/111e78a3-c348-425c-8749-215068a39571

import Mathlib

theorem solution
    (C U L VR VL I O residue : ℂ)
    (hdecomp : C = U + L + VR + VL + I + O)
    (hres : C = 2 * Real.pi * Complex.I * residue) :
    U + L + VR + VL + I + O = 2 * Real.pi * Complex.I * residue := by
  rw [← hdecomp]
  exact hres
