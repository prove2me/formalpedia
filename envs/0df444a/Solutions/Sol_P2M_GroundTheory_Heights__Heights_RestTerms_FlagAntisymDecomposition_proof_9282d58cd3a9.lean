-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagAntisymDecomposition_proof_9282d58cd3a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:59.425837+00:00
-- url     : https://prove2.me/submissions/23c2125a-2018-41bb-88be-887673486b5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagAntisymDecomposition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_finset_sum_5e781c993071

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
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagAntisymDecomposition
theorem _root_.solution (h1 : FlagSymmetricMulAntisym.Statement)
    (h2 : FlagPowerSumSymmetric.Statement) : FlagAntisymDecomposition.Statement := by
  intro f N F G Q R hF hR
  rw [hF, Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_left_comm, h1 f N _ _ (h2 f N l σ), hR, mul_left_comm]
end FlagAntisymDecomposition
end GroundTheory.Heights₂.Heights.RestTerms
