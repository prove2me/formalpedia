-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_prod_39abdaefbbe5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:38.927192+00:00
-- url     : https://prove2.me/submissions/eecc1671-793c-4d80-8bcb-02e9bc982ae7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockPermute_blockEmb_50bfbd9b99dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_one_eq_721afeca8374

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
theorem _root_.solution (f N : ℕ) (P : Fin f → RootRing 1 N) :
    antisymmetrize f N (∏ σ, blockEmb f N σ (P σ)) =
      ∏ σ, blockEmb f N σ (antisymmetrize 1 N (P σ)) := by
  simp_rw [antisymmetrize_one_eq, map_sum, Finset.prod_univ_sum, antisymmetrize, map_prod,
    blockPermute_blockEmb, map_smul]
  refine Finset.sum_congr (by simp) fun w _ => ?_
  simp only [blockSign, smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
end GroundTheory.Heights₂.Heights.RestTerms.Top
