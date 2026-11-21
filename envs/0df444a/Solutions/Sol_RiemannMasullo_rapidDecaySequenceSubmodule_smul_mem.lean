-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceSubmodule_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:24:27.913171+00:00
-- url     : https://prove2.me/submissions/54ce12dd-e5b5-4823-9283-c6261417819e

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L531-L533
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution (c : ℂ) {s : (Fin r → ℤ) → ℂ}
    (hs : ∀ j, rapidDecaySequenceBound j s < ⊤) :
    ∀ j, rapidDecaySequenceBound j (c • s) < ⊤ := by
  intro j
  apply lt_of_le_of_lt _ (ENNReal.mul_lt_top (ENNReal.coe_lt_top (r := ‖c‖₊)) (hs j))
  unfold rapidDecaySequenceBound
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro a
  simp only [Pi.smul_apply, smul_eq_mul, nnnorm_mul, ENNReal.coe_mul]
  exact le_of_eq (mul_left_comm _ _ _)
