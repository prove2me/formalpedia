-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_smallBlockPlace_eq_24505b87eaf7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:31.517787+00:00
-- url     : https://prove2.me/submissions/1d5b2af3-dbb0-4a78-a24f-8993de20d724

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAntisymmetrizePlace

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
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (x : Fin r ⊕ Fin a) :
    smallBlockPlace r a c x = (0, smallBlockPlaceEquiv r a c x) := by
  exact Prod.ext (Subsingleton.elim _ _) rfl
end GroundTheory.Heights₂.Heights.RestTerms
