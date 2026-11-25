-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_prod_e3381b56d30a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:09.123036+00:00
-- url     : https://prove2.me/submissions/7757140b-b75f-4622-9abd-38d8e6770859

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockVandermonde_eq_prod_c4f2ba1d0b15
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_prod_39abdaefbbe5

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
theorem _root_.solution (f N : ℕ) (P Q : Fin f → RootRing 1 N) (h : ∀ σ, HasDD 1 N (P σ) (Q σ)) :
    HasDD f N (∏ σ, blockEmb f N σ (P σ)) (∏ σ, blockEmb f N σ (Q σ)) := by
  rw [HasDD, antisymmetrize_prod, blockVandermonde_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [h σ, map_mul]
end GroundTheory.Heights₂.Heights.RestTerms.Top
