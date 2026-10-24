-- Prove2me | solution 1 for bounded_set_volume_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:04:45.064984+00:00
-- url     : https://prove2.me/submissions/7702cfe9-083e-4a21-a3ab-4b7e5a993d48

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem solution
    {n : Nat} (s : Set (Fin n → Real)) (hs : Bornology.IsBounded s) :
    MeasureTheory.volume s ≠ ⊤ := by
  exact hs.measure_lt_top.ne