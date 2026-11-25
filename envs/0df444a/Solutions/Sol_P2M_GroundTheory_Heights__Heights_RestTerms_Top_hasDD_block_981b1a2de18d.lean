-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_block_981b1a2de18d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:37:40.068079+00:00
-- url     : https://prove2.me/submissions/e726dc53-fc6d-4d93-b6fe-63c9e5081a8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_sum_ee2bd3fc8234
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_extraFactor_expand_3ef494201fb2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (hF : FrobeniusCharacterFormula.Statement) (r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (q m : ℕ) :
    HasDD 1 (r + a) (yEval r a c (extraFactor r q * psum (Fin r) ℚ 1 ^ m) * fib1 r a c)
      (blockOut r a c κ q m) := by
  rw [extraFactor_expand hF]
  exact hasDD_schur_sum r a c κ hκ _ (fun lam h => antitone_of_mem_partitionsOf h) _
end GroundTheory.Heights₂.Heights.RestTerms.Top
