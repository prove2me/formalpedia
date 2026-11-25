-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_proof_069af04e8b17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:20.020909+00:00
-- url     : https://prove2.me/submissions/3e23e79b-4b19-4c94-820c-881b55ae247d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchConcatAlternant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_comp_perm_6bc028974320
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_add_staircase_3c7cb7a968da
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_padPartition_94764fcf450d


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
namespace SchConcatAlternant
theorem _root_.solution (h1 : SchAlternantRenamePlace.Statement)
    (h2 : SchConcatExponent.Statement) : SchConcatAlternant.Statement := by
  intro r a c
  obtain ⟨τ, hτ⟩ := h2 r a c
  refine ⟨((Equiv.Perm.sign τ : ℤ) : ℚ), ?_, fun lam hlam => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  · rw [h1, hτ lam hlam, SchConcatAlternant.alternant_comp_perm,
      SchConcatAlternant.alternant_add_staircase,
      Schur.schur_padPartition (Fin (r + a)) (fun i : Fin r => lam i - a) (r + a) (by omega), map_mul,
      rename_C]
end SchConcatAlternant
end GroundTheory.Heights₂.Heights.RestTerms
