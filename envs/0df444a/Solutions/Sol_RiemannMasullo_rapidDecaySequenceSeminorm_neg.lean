-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceSeminorm_neg
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:38:41.244172+00:00
-- url     : https://prove2.me/submissions/a70c658a-417f-4a04-a974-da764e13a834

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L568-L570
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution (j : ℕ) (s : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (-s).val).toReal = (rapidDecaySequenceBound j s.val).toReal :=
  by
  change (rapidDecaySequenceBound j (-s.val)).toReal = _
  simp [rapidDecaySequenceBound]
