-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_RestTerms_rectangle_antitone_inhabited_4ef6eb5014ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:52.956802+00:00
-- url     : https://prove2.me/submissions/17dbe82b-ce89-4757-a91f-6424b0d48e10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution : Antitone (rectangle 2 3) := fun _ _ _ => le_rfl
end GroundTheory.Heights₂.Heights.RestTerms
