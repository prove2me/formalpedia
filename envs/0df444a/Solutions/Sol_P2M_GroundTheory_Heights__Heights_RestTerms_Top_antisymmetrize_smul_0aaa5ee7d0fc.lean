-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_smul_0aaa5ee7d0fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:02.699721+00:00
-- url     : https://prove2.me/submissions/9909ba8a-5726-4484-8f14-1840f10d5d94

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
theorem _root_.solution (f N : ℕ) (b : ℚ) (H : RootRing f N) :
    antisymmetrize f N (b • H) = b • antisymmetrize f N H := by
  simp [antisymmetrize, map_smul, Finset.smul_sum, smul_comm b]
end GroundTheory.Heights₂.Heights.RestTerms.Top
