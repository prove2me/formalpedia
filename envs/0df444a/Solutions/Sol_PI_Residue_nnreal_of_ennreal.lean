-- Prove2me | solution 1 for PI.Residue.nnreal_of_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:39.69156+00:00
-- url     : https://prove2.me/submissions/4b4bfce4-38bd-47cd-b7b1-48015d521804

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NnrealOfEnnreal

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
theorem _root_.solution {β : Type*} (f : β → ℝ≥0) (g : ℕ → ℝ≥0) (m : ℕ) (hg : Summable g)
    (h : ∑' b, (f b : ℝ≥0∞) ≤ (∑' k, (g k : ℝ≥0∞)) ^ m) :
    Summable f ∧ ∑' b, f b ≤ (∑' k, g k) ^ m := by
  rw [← ENNReal.coe_tsum hg, ← ENNReal.coe_pow] at h
  have hf : Summable f :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (ne_top_of_le_ne_top ENNReal.coe_ne_top h)
  refine ⟨hf, ?_⟩
  rw [← ENNReal.coe_tsum hf] at h
  exact_mod_cast h
end PI.Residue
