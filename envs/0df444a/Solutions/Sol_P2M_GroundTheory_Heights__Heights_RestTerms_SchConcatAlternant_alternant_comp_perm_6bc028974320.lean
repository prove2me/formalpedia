-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_comp_perm_6bc028974320
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:41.424079+00:00
-- url     : https://prove2.me/submissions/196e06c2-c2c6-4bab-bcd4-ba07fe56e7fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchConcatAlternant

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
theorem _root_.solution {N : ℕ} (w : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    alternant (w ∘ τ) = C ((Equiv.Perm.sign τ : ℤ) : ℚ) * alternant w := by
  unfold alternant
  have hM : (Matrix.of fun i i' : Fin N =>
      (X i : MvPolynomial (Fin N) ℚ) ^ (w ∘ τ) i') =
      (Matrix.of fun i i' : Fin N => (X i : MvPolynomial (Fin N) ℚ) ^ w i').submatrix id τ := rfl
  rw [hM, Matrix.det_permute', map_intCast]
end SchConcatAlternant
end GroundTheory.Heights₂.Heights.RestTerms
