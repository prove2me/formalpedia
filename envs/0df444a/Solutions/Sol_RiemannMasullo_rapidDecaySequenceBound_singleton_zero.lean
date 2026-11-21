-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceBound_singleton_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:33:43.096832+00:00
-- url     : https://prove2.me/submissions/1be50100-77e0-4560-949c-f1b78a3c40c1

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L513-L515
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution (j : ℕ) (c : ℂ) :
    rapidDecaySequenceBound (r := r) j (({0} : Set (Fin r → ℤ)).indicator (fun _ ↦ c)) =
      (‖c‖₊ : ℝ≥0∞) := by
  classical
  unfold rapidDecaySequenceBound
  rw [tsum_eq_single (0 : Fin r → ℤ)]
  · simp
    change (1 + (‖(0 : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^ j * _ = _
    simp
  · intro a ha
    simp [Set.indicator_of_notMem,ha]
