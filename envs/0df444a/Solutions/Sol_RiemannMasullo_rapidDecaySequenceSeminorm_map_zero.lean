-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceSeminorm_map_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:38:40.02089+00:00
-- url     : https://prove2.me/submissions/96163ade-ac99-4862-ad88-20d96008d772

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L550-L551
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution (j : ℕ) :
    (rapidDecaySequenceBound j (0 : rapidDecaySequenceSubmodule r).val).toReal = 0 := by
  change (rapidDecaySequenceBound j (0 : (Fin r → ℤ) → ℂ)).toReal = 0
  simp [rapidDecaySequenceBound]
