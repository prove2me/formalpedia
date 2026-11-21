-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceSeminorm_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:43:02.396415+00:00
-- url     : https://prove2.me/submissions/7e8d273a-d170-4e65-993f-75e34c3f1365

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L591-L592
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution (s : RapidDecaySequence r) :
    rapidDecaySequenceSeminorm 0 s = ∑' a, ‖s a‖ := by
  change (rapidDecaySequenceBound 0 s.val).toReal = _
  simp only [rapidDecaySequenceBound, pow_zero, one_mul]
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.coe_ne_top)]
  rfl
