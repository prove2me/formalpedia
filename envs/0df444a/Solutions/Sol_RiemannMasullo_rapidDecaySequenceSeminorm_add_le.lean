-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceSeminorm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:38:40.688177+00:00
-- url     : https://prove2.me/submissions/ce62dfe6-9652-41ed-8350-8d6d49008ecb

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L555-L558
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution (j : ℕ) (s t : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (s + t).val).toReal ≤
      (rapidDecaySequenceBound j s.val).toReal + (rapidDecaySequenceBound j t.val).toReal :=
  by
  change (rapidDecaySequenceBound j (s.val+t.val)).toReal ≤ _
  rw [← ENNReal.toReal_add (s.property j).ne (t.property j).ne]
  apply ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨s.property j,t.property j⟩).ne
  unfold rapidDecaySequenceBound
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro a
  rw [← mul_add, ← ENNReal.coe_add]
  exact mul_le_mul_of_nonneg_left (ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)) (by positivity)
