-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockVandermonde_eq_prod_c4f2ba1d0b15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:43.575802+00:00
-- url     : https://prove2.me/submissions/a5bd171c-90df-4e2d-b6a9-c9b4d26c8a47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_blockVandermonde_e3beae7d792c

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
theorem _root_.solution (f N : ℕ) :
    blockVandermonde f N = ∏ σ : Fin f, blockEmb f N σ (blockVandermonde 1 N) := by
  simp only [blockEmb_blockVandermonde]
  rfl
end GroundTheory.Heights₂.Heights.RestTerms.Top
