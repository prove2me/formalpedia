-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternantZero_proof_d152d7ddc0f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:44.693596+00:00
-- url     : https://prove2.me/submissions/51fdc808-83bd-47d2-845b-7d2fe45c68c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchConcatAlternantZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchConcatAlternantZero
theorem _root_.solution : SchConcatAlternantZero.Statement := by
  intro r a lam hanti hnot
  have hex : ∃ i, lam i < a := by
    by_contra h
    exact hnot fun i => not_lt.mp fun hi => h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let k : Fin r := ⟨r - 1, by omega⟩
  have hkv : (k : ℕ) = r - 1 := rfl
  have hik : i ≤ k := by
    rw [Fin.le_def, hkv]; omega
  have hka : lam k < a := lt_of_le_of_lt (hanti hik) hi
  let j : Fin a := ⟨a - 1 - lam k, by omega⟩
  have hjv : (j : ℕ) = a - 1 - lam k := rfl
  have hexp : lam k + (r - 1 - (k : ℕ)) = a - 1 - (j : ℕ) := by
    rw [hkv, hjv]; omega
  unfold alternant
  apply Matrix.det_zero_of_column_eq (i := Sum.inl k) (j := Sum.inr j) Sum.inl_ne_inr
  intro p
  simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hexp]
end SchConcatAlternantZero
end GroundTheory.Heights₂.Heights.RestTerms
