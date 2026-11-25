-- Prove2me | solution 1 for PI.Residue.tsum_ideal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:39.099803+00:00
-- url     : https://prove2.me/submissions/c3a38a10-07ee-446a-9849-7412dd6f194c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
import Theorems.Thm_PI_Residue_exists_tuple
import Theorems.Thm_PI_Residue_tsum_le_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField Ideal UniqueFactorizationMonoid
open scoped ENNReal
variable (E : Type*) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
variable (E)
namespace PI.Residue
theorem _root_.solution (w : ℕ →* ℝ≥0∞) :
    ∑' I : {I : Ideal (𝓞 E) // I ≠ ⊥}, w (absNorm I.1) ≤ (∑' k, w k) ^ Module.finrank ℚ E := by
  obtain ⟨n, hinj, hn⟩ := exists_tuple E
  refine tsum_le_pow n hinj w _ (fun I => ?_)
  rw [← hn I, map_prod]
end PI.Residue
