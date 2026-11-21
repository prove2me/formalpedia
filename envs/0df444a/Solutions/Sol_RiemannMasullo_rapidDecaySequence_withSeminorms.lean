-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequence_withSeminorms
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:43:30.209222+00:00
-- url     : https://prove2.me/submissions/aa4041a6-da2b-418a-9c95-ac936ce42717

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L596-L597
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution :
    WithSeminorms (E := RapidDecaySequence r) rapidDecaySequenceSeminorm := by
  exact ⟨rfl⟩
