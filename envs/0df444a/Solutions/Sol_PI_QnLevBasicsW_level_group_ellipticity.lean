-- Prove2me | solution 1 for PI.QnLevBasicsW.level_group_ellipticity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:43:49.515808+00:00
-- url     : https://prove2.me/submissions/e10d8c3c-2814-4ed7-b64a-974b233abfd2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_in_8b7430a5315f
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_out_3fcd34e8e182
import Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_in
import Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_out
import Theorems.Thm_PI_QnLevBasicsW_mulVec_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution : LevEll := by
  intro k i r' z g
  unfold ell
  rw [Fin.sum_univ_add]
  refine Eq.trans (congrArg (· + _) (Finset.sum_eq_zero ?_)) ?_
  · intro a _
    have ha := a.isLt
    have hp : ¬ (i ≤ (eI k (i + r') (Fin.castAdd r' a)).val ∧
        (eI k (i + r') (Fin.castAdd r' a)).val < 2 * r' + k + 1 + i) := by
      simp only [eI, Fin.val_mk, Fin.coe_castAdd]; omega
    split_ifs with h
    · rw [ιLev_apply_out g _ _ hp, if_neg]
      intro e
      have := congrArg Fin.val e
      simp only [eI, Fin.val_mk, Fin.coe_castAdd] at this
      omega
    · rw [mulVec_lift, liftVec_apply_out _ _ hp]
  · rw [zero_add]
    apply Finset.sum_congr rfl
    intro b _
    have hb := b.isLt
    split_ifs with h1 h2 h3
    · apply ιLev_apply_in <;> simp only [eI, Fin.val_mk, Fin.coe_natAdd] <;> omega
    · exfalso
      simp only [Fin.coe_natAdd] at h1
      omega
    · exfalso
      simp only [Fin.coe_natAdd] at h1
      omega
    · rw [mulVec_lift]
      apply liftVec_apply_in
      simp only [eI, Fin.val_mk, Fin.coe_natAdd]
      omega
end PI.QnLevBasicsW
