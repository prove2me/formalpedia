-- Prove2me | solution 1 for PI.QnLevBasicsW.col_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:33:46.864657+00:00
-- url     : https://prove2.me/submissions/6d5dd7ea-1324-4eb2-8f7b-99f2f944d723

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_out_3fcd34e8e182
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_in_out_b74a29dc527c
import Theorems.Thm_PI_QnLevBasicsW_bvec_lift
import Theorems.Thm_PI_QnLevBasicsW_mulVec_bvec
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
theorem _root_.solution (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (q : Fin (2 * (i + r') + k + 1))
    (h : ∀ a : Fin (2 * r' + k + 1), q.val = a.val + i → g *ᵥ bvec a = bvec a) :
    ιLev k i r' g *ᵥ bvec q = bvec q := by
  by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
  · have hqa : q.val - i < 2 * r' + k + 1 := by omega
    have e : q.val = (⟨q.val - i, hqa⟩ : Fin (2 * r' + k + 1)).val + i := by simp only [Fin.val_mk]; omega
    rw [← bvec_lift ⟨q.val - i, hqa⟩ q e, mulVec_lift, h _ e]
  · funext p
    rw [mulVec_bvec]
    by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · rw [ιLev_apply_in_out g p q hp hq]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro e
      rw [e] at hp
      exact hq hp
    · rw [ιLev_apply_out g p q hp]
      simp [bvec, Pi.single_apply]
end PI.QnLevBasicsW
