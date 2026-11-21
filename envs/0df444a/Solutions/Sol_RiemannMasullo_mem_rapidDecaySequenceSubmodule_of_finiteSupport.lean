-- Prove2me | solution 1 for RiemannMasullo.mem_rapidDecaySequenceSubmodule_of_finiteSupport
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:38:39.352803+00:00
-- url     : https://prove2.me/submissions/e2630827-a0de-4824-b05d-77b8b8f0144a

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L545-L547
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution (s : (Fin r → ℤ) → ℂ)
    (hs : (Function.support s).Finite) :
    s ∈ rapidDecaySequenceSubmodule r := by
  classical
  intro j
  unfold rapidDecaySequenceBound
  rw [tsum_eq_sum (s := hs.toFinset)]
  · apply ENNReal.sum_lt_top.mpr
    intro a _
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.add_lt_top.mpr ⟨by simp, ENNReal.coe_lt_top⟩)) ENNReal.coe_lt_top
  · intro a ha
    have h : s a = 0 := by simpa [Function.support] using ha
    simp [h]
