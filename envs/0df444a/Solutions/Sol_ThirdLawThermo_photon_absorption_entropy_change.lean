-- Prove2me | solution 1 for ThirdLawThermo.photon_absorption_entropy_change
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:11:27.429022+00:00
-- url     : https://prove2.me/submissions/e2e3e11d-f31a-46fd-9ec0-98f10662ea69

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology
open ThirdLawThermo

theorem solution (kB : ℝ) (N : ℕ) :
    boltzmannEntropy kB N - boltzmannEntropy kB 1 = kB * Real.log N := by
  simp [boltzmannEntropy]
