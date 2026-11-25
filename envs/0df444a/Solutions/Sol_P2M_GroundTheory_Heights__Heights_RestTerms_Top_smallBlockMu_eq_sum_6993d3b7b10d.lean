-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallBlockMu_eq_sum_6993d3b7b10d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:08.973161+00:00
-- url     : https://prove2.me/submissions/c0b834a4-bf0a-49c8-826f-e7fd627ccd78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_yRoot_eq_blockEmb_3d7bdf650708

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
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) :
    smallBlockMu f r a c = ∑ σ : Fin f, blockEmb f (r + a) σ (yEval r a c (psum (Fin r) ℚ 1)) := by
  simp only [yEval, psum, map_sum, pow_one, aeval_X, smallBlockMu]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => ?_
  rw [yRoot_eq_blockEmb f r a c σ i]
end GroundTheory.Heights₂.Heights.RestTerms.Top
