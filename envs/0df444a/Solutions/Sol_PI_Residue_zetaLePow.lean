-- Prove2me | solution 1 for PI.Residue.zetaLePow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:14.846914+00:00
-- url     : https://prove2.me/submissions/15872627-34be-4cb0-beeb-590a03b661fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NnrealOfEnnreal
import Theorems.Thm_PI_Residue_wt_apply
import Theorems.Thm_PI_Residue_nnreal_of_ennreal
import Theorems.Thm_PI_Residue_tsum_ideal_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField
open scoped ENNReal NNReal
namespace PI.Residue
theorem _root_.solution : ZetaLePow := by
  intro E _ _ s hs
  have h := tsum_ideal_le E (wt s)
  have h0 : wt s 0 = 0 := by
    rw [wt_apply, Nat.cast_zero, NNReal.zero_rpow (by linarith : -s ≠ 0), ENNReal.coe_zero]
  rw [tsum_eq_zero_add' ENNReal.summable, h0, zero_add] at h
  simp only [wt_apply] at h
  have hg : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0) ^ (-s))) := by
    rw [← NNReal.summable_coe]
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s < -1))
    simpa using this
  obtain ⟨hf, hle⟩ := nnreal_of_ennreal
    (fun I : {I : Ideal (𝓞 E) // I ≠ ⊥} => ((Ideal.absNorm I.1 : ℝ≥0) ^ (-s))) _ _ hg h
  constructor
  · have := NNReal.summable_coe.mpr hf
    simpa using this
  · have := NNReal.coe_le_coe.mpr hle
    rw [NNReal.coe_tsum, NNReal.coe_pow, NNReal.coe_tsum] at this
    simpa [idealZeta, zetaR] using this
end PI.Residue
