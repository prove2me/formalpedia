-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_add_c1cef20a7e70
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:21.562767+00:00
-- url     : https://prove2.me/submissions/0a002a1a-c240-4eb4-bee7-592c50fee621

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand

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
theorem _root_.solution (f N : ℕ) (H H' : RootRing f N) :
    antisymmetrize f N (H + H') = antisymmetrize f N H + antisymmetrize f N H' := by
  simp [antisymmetrize, map_add, smul_add, Finset.sum_add_distrib]
end GroundTheory.Heights₂.Heights.RestTerms.Top
