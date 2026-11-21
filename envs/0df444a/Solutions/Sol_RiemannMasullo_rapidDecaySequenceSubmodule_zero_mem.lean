-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceSubmodule_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:24:27.153204+00:00
-- url     : https://prove2.me/submissions/8d7057bf-2f08-4901-8bb2-c4753899655d

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L519-L520
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution :
    ∀ j, rapidDecaySequenceBound j (0 : (Fin r → ℤ) → ℂ) < ⊤ := by
  intro j
  simp [rapidDecaySequenceBound]
