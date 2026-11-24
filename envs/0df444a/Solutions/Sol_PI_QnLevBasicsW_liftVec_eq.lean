-- Prove2me | solution 1 for PI.QnLevBasicsW.liftVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:35:47.30781+00:00
-- url     : https://prove2.me/submissions/8d8dda28-209b-4210-be34-51e68b9d307c

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Theorems.Thm_PI_QnLevBasicsW_split_symm_inl
import Theorems.Thm_PI_QnLevBasicsW_split_symm_inr

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
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' v = (Sum.elim v 0) ∘ (split k i r') := by
  funext p
  obtain ⟨s, rfl⟩ := (split k i r').symm.surjective p
  rw [Function.comp_apply, Equiv.apply_symm_apply]
  simp only [liftVec]
  rcases s with a | b
  · have ha := a.isLt
    have h1 : i ≤ ((split k i r').symm (Sum.inl a)).val ∧ ((split k i r').symm (Sum.inl a)).val < 2 * r' + k + 1 + i := by rw [split_symm_inl]; omega
    rw [dif_pos h1, Sum.elim_inl]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk, split_symm_inl]
    omega
  · have hb := b.isLt
    have h1 : ¬(i ≤ ((split k i r').symm (Sum.inr b)).val ∧ ((split k i r').symm (Sum.inr b)).val < 2 * r' + k + 1 + i) := by rw [split_symm_inr]; split_ifs <;> omega
    rw [dif_neg h1, Sum.elim_inr, Pi.zero_apply]
end PI.QnLevBasicsW
