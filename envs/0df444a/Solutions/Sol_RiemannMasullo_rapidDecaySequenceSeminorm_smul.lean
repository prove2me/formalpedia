-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequenceSeminorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:38:10.218466+00:00
-- url     : https://prove2.me/submissions/92ac2f33-25f1-4980-bb48-e5a2272b3085

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L562-L564
import Mathlib
import Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
open RiemannMasullo
open scoped ENNReal
variable {r : ℕ}
theorem solution (j : ℕ) (c : ℂ) (s : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (c • s).val).toReal =
      ‖c‖ * (rapidDecaySequenceBound j s.val).toReal := by
  change (rapidDecaySequenceBound j (c • s.val)).toReal = _
  have he : rapidDecaySequenceBound j (c • s.val) = (‖c‖₊ : ℝ≥0∞) * rapidDecaySequenceBound j s.val := by
    unfold rapidDecaySequenceBound
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro a
    simp only [Pi.smul_apply, smul_eq_mul, nnnorm_mul, ENNReal.coe_mul]
    exact mul_left_comm _ _ _
  rw [he, ENNReal.toReal_mul]
  rfl
