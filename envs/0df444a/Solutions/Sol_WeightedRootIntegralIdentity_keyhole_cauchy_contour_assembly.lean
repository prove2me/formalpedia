-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyhole_cauchy_contour_assembly
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T12:31:16.362668+00:00
-- url     : https://prove2.me/submissions/846cc430-957a-42d9-a820-e5b831b7c038

import Mathlib

theorem solution
    (Iupper Ilower Iinner Iouter residue : ℂ)
    (hboundary : Iupper + Ilower + Iinner + Iouter = 2 * Real.pi * Complex.I * residue)
    (hbank : Iupper + Ilower = 2 * Complex.I * (Iupper / (2 * Complex.I)))
    (harcs : Iinner + Iouter = 0) :
    Iupper / (2 * Complex.I) = Real.pi * residue := by
  have hne : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  field_simp [hne] at hbank ⊢
  linear_combination hboundary - harcs - hbank
