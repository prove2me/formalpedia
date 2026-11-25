-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvariantTopDegree_proof_ba21560137f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:56.795281+00:00
-- url     : https://prove2.me/submissions/ea65bf73-3469-4db9-9aeb-3de8db4507b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvariantTopDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_monomial_staircase_eq_c1973ddcf09b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_rat_eq_1ba39560cb25

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
namespace CoinvariantTopDegree
theorem _root_.solution (h1 : CoinvAtTop.Statement) : CoinvariantTopDegree.Statement := by
  intro f N H hH
  obtain ⟨c, hc⟩ := h1 ℚ f N H hH
  refine ⟨c, ?_⟩
  rw [← Coinv.monomial_staircase_eq, ← Coinv.psumIdeal_rat_eq]
  exact hc
end CoinvariantTopDegree
end GroundTheory.Heights₂.Heights.RestTerms
