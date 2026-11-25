-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_abs_cf_perm_755c477b2285
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:59.851388+00:00
-- url     : https://prove2.me/submissions/9d5b7bcd-f762-41a5-a284-4c0d4ce47c99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_perm_129463b0e566


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
open MvPolynomial Finset Equiv Comb
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
namespace GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
theorem _root_.solution {m : ℕ} {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m))
    (v : Fin m → ℕ) : |cf (v ∘ σ.symm) P| = |cf v P| := by
  rw [cf_perm hP σ v, abs_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
end GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
