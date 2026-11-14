-- Prove2me | solution 1 for PGDRevision20261113.error_band_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T06:36:32.598449+00:00
-- url     : https://prove2.me/submissions/1749d913-9d54-42b2-a686-1bf3bfc59c5d

import Definitions.Def_PGDRevision20261113_Profile
import Mathlib.Tactic.Linarith

open PGDRevision20261113

theorem solution : ErrorBandEquivalenceClaim := by
  intro A B v R hA hB hv hR hR1
  have hvB : 0 < v + B := add_pos hv hB
  have hplus : 0 < 1 + R := by linarith
  have hminus : 0 < 1 - R := by linarith
  unfold lowerBand upperBand
  rw [abs_le]
  constructor
  · rintro ⟨hl, hu⟩
    have hl' := (le_div_iff₀ hvB).mp hl
    have hu' := (div_le_iff₀ hvB).mp hu
    constructor
    · apply (div_le_iff₀ hplus).mpr
      nlinarith
    · apply (le_div_iff₀ hminus).mpr
      nlinarith
  · rintro ⟨hl, hu⟩
    have hl' := (div_le_iff₀ hplus).mp hl
    have hu' := (le_div_iff₀ hminus).mp hu
    constructor
    · apply (le_div_iff₀ hvB).mpr
      nlinarith
    · apply (div_le_iff₀ hvB).mpr
      nlinarith
