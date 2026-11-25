-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_sum_update_sub_one_1c80aec9c4ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:04.543881+00:00
-- url     : https://prove2.me/submissions/beefd335-0e87-4411-adbb-0582c290a722

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfMonomialPsumOne

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
open MvPolynomial Finset Comb
open GroundTheory.Heights₂.Heights.RestTerms.CombCfMonomialPsumOne
namespace GroundTheory.Heights₂.Heights.RestTerms.CombCfMonomialPsumOne
theorem _root_.solution {m : ℕ} (l : Fin m → ℕ) (i : Fin m) (h : 1 ≤ l i) :
    ∑ j, Function.update l i (l i - 1) j + 1 = ∑ j, l j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) l]
  omega
end GroundTheory.Heights₂.Heights.RestTerms.CombCfMonomialPsumOne
