-- Prove2me | solution 1 for PI.QnLevBasicsW.Hpk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:23:06.38011+00:00
-- url     : https://prove2.me/submissions/cd02c6ef-558a-4b4f-8fb5-16b313b5cec6

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
theorem _root_.solution :
    Hpk k (i + r') = (fromBlocks (Hpk k r') 0 0 (Jrest k i r')).submatrix (split k i r') (split k i r') := by
  ext p q
  rw [Matrix.submatrix_apply]
  obtain ⟨s, rfl⟩ := (split k i r').symm.surjective p
  obtain ⟨t, rfl⟩ := (split k i r').symm.surjective q
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rcases s with a | b <;> rcases t with a' | b'
  · rw [fromBlocks_apply₁₁]
    have ha := a.isLt
    have ha' := a'.isLt
    have e1 := split_symm_inl (k := k) (i := i) (r' := r') a
    have e2 := split_symm_inl (k := k) (i := i) (r' := r') a'
    simp only [Hpk, Fin.ext_iff, e1, e2]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    have ha := a.isLt
    have hb := b'.isLt
    have e1 := split_symm_inl (k := k) (i := i) (r' := r') a
    have e2 := split_symm_inr (k := k) (i := i) (r' := r') b'
    simp only [Hpk, Fin.ext_iff, e1, e2]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    have hb := b.isLt
    have ha := a'.isLt
    have e1 := split_symm_inr (k := k) (i := i) (r' := r') b
    have e2 := split_symm_inl (k := k) (i := i) (r' := r') a'
    simp only [Hpk, Fin.ext_iff, e1, e2]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [fromBlocks_apply₂₂]
    rfl
end PI.QnLevBasicsW
