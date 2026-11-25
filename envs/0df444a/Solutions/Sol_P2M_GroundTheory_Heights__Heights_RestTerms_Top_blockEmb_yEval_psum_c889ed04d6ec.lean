-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_yEval_psum_c889ed04d6ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:53:36.685918+00:00
-- url     : https://prove2.me/submissions/4b6dd2e1-6dc7-4fa4-921c-0a127de6b70c

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
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (k : ℕ) :
    blockEmb f (r + a) σ (yEval r a c (psum (Fin r) ℚ k)) = smallPowerSum f r a c k σ := by
  simp only [yEval, psum, map_sum, map_pow, aeval_X, smallPowerSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [yRoot_eq_blockEmb f r a c σ i]
end GroundTheory.Heights₂.Heights.RestTerms.Top
