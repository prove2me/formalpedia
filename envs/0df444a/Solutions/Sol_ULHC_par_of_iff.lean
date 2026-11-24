-- Prove2me | solution 1 for ULHC.par_of_iff
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:28:04.535502+00:00
-- url     : https://prove2.me/submissions/9be89a2d-53b9-423f-bde6-74de01ad72d2

import Mathlib


theorem solution {a b : ℕ} (h : a % 2 = 1 ↔ b % 2 = 1) : a % 2 = b % 2 := by
  omega
