-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_finset_sum_5e781c993071
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:58.655907+00:00
-- url     : https://prove2.me/submissions/3d055b71-3e3f-470d-b10a-32464ff5f861

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagAntisymDecomposition

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
theorem _root_.solution (f N : ℕ) {ι : Type*} (s : Finset ι) (g : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, g i) = ∑ i ∈ s, antisymmetrize f N (g i) := by
  simp only [antisymmetrize, map_sum, Finset.smul_sum]
  exact Finset.sum_comm
end GroundTheory.Heights₂.Heights.RestTerms
