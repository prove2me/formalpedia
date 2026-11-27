-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_vandermondePsumOne_cfde9b8cac77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:12:15.695325+00:00
-- url     : https://prove2.me/submissions/9f852e0d-7d24-4c10-8090-033c90c6f8a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsComb

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
open MvPolynomial Finset Equiv Comb
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Comb
theorem _root_.solution :
    ∑ i, (![2, 0] : Fin 2 → ℕ) i = ∑ i, stair 2 i + 1 := by
  simp [Fin.sum_univ_two, stair]
end Comb
end GroundTheory.Heights₂.Heights.RestTerms
