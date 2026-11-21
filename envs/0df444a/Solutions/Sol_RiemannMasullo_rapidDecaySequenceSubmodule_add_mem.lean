-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceSubmodule_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:33:44.138479+00:00
-- url     : https://prove2.me/submissions/6e80b5c5-1e72-4cee-998e-79aabd9e472a

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L524-L527
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution {s t : (Fin r → ℤ) → ℂ}
    (hs : ∀ j, rapidDecaySequenceBound j s < ⊤)
    (ht : ∀ j, rapidDecaySequenceBound j t < ⊤) :
    ∀ j, rapidDecaySequenceBound j (s + t) < ⊤ := by
  intro j
  apply lt_of_le_of_lt _ (ENNReal.add_lt_top.mpr ⟨hs j,ht j⟩)
  unfold rapidDecaySequenceBound
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro a
  rw [← mul_add, ← ENNReal.coe_add]
  exact mul_le_mul_of_nonneg_left (ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)) (by positivity)
