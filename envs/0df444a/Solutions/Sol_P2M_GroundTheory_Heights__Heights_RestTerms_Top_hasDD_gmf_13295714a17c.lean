-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:44:53.495242+00:00
-- url     : https://prove2.me/submissions/b6ac1328-10bd-4d9f-9264-8bd74333ee3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_expand_blocks_7e6ac51297a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_block_981b1a2de18d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_prod_e3381b56d30a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_smul_1cdeb56450cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_sum_332cef462e63


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
theorem _root_.solution (hF : FrobeniusCharacterFormula.Statement) (f r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (q : Fin f → ℕ) (e : ℕ) :
    HasDD f (r + a) (gmf f r a c q e) (gmfOut f r a c κ q e) := by
  rw [gmf, expand_blocks, gmfOut]
  refine hasDD_sum _ fun m _ => hasDD_smul _ (hasDD_prod f (r + a) _ _ fun σ => ?_)
  exact hasDD_block hF r a c κ hκ (q σ) (m σ)
end GroundTheory.Heights₂.Heights.RestTerms.Top
