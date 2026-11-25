-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_succ_a74d7db17473
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:57.181375+00:00
-- url     : https://prove2.me/submissions/c05b2454-62c1-4408-a2ef-836d4c5154c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
theorem _root_.solution {t : ℕ} (n : Fin t → ℕ) (c : ℤ) :
    numPt n (c + 1) = numPt n c + Pi.single (Fin.last t) 1 := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [numPt]
  | cast i => simp [numPt, Fin.castSucc_ne_last]
end GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
