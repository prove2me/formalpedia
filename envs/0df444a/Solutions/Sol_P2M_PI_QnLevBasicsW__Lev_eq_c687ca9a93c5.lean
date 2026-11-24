-- Prove2me | solution 1 for P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:55:45.494438+00:00
-- url     : https://prove2.me/submissions/a49d2cfc-3435-4f43-af3b-c5a5aace561a

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
theorem _root_.solution (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    ιLev k i r' g = (fromBlocks g 0 0 1).submatrix (split k i r') (split k i r') := by
  ext p q
  rw [Matrix.submatrix_apply]
  obtain ⟨s, rfl⟩ := (split k i r').symm.surjective p
  obtain ⟨t, rfl⟩ := (split k i r').symm.surjective q
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [ιLev]
  rcases s with a | b <;> rcases t with a' | b'
  · have ha := a.isLt
    have ha' := a'.isLt
    have h1 : i ≤ ((split k i r').symm (Sum.inl a)).val ∧ ((split k i r').symm (Sum.inl a)).val < 2 * r' + k + 1 + i := by rw [split_symm_inl]; omega
    have h2 : i ≤ ((split k i r').symm (Sum.inl a')).val ∧ ((split k i r').symm (Sum.inl a')).val < 2 * r' + k + 1 + i := by rw [split_symm_inl]; omega
    rw [dif_pos h1, dif_pos h2, fromBlocks_apply₁₁]
    congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk, split_symm_inl] <;> omega
  · have ha := a.isLt
    have hb := b'.isLt
    have h1 : i ≤ ((split k i r').symm (Sum.inl a)).val ∧ ((split k i r').symm (Sum.inl a)).val < 2 * r' + k + 1 + i := by rw [split_symm_inl]; omega
    have h2 : ¬(i ≤ ((split k i r').symm (Sum.inr b')).val ∧ ((split k i r').symm (Sum.inr b')).val < 2 * r' + k + 1 + i) := by rw [split_symm_inr]; split_ifs <;> omega
    rw [dif_pos h1, dif_neg h2, fromBlocks_apply₁₂, Matrix.zero_apply]
  · have hb := b.isLt
    have ha := a'.isLt
    have h1 : ¬(i ≤ ((split k i r').symm (Sum.inr b)).val ∧ ((split k i r').symm (Sum.inr b)).val < 2 * r' + k + 1 + i) := by rw [split_symm_inr]; split_ifs <;> omega
    rw [dif_neg h1, fromBlocks_apply₂₁, Matrix.zero_apply, if_neg]
    intro e
    exact Sum.inr_ne_inl ((split k i r').symm.injective e)
  · have hb := b.isLt
    have h1 : ¬(i ≤ ((split k i r').symm (Sum.inr b)).val ∧ ((split k i r').symm (Sum.inr b)).val < 2 * r' + k + 1 + i) := by rw [split_symm_inr]; split_ifs <;> omega
    rw [dif_neg h1, fromBlocks_apply₂₂, Matrix.one_apply]
    by_cases e : b = b'
    · subst e
      simp
    · have hne : (split k i r').symm (Sum.inr b) ≠ (split k i r').symm (Sum.inr b') :=
        fun h => e (Sum.inr_injective ((split k i r').symm.injective h))
      rw [if_neg hne, if_neg e]
end PI.QnLevBasicsW
