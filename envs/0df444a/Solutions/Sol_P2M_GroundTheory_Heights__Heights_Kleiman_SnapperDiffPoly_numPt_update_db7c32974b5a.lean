-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_update_db7c32974b5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:19.541903+00:00
-- url     : https://prove2.me/submissions/4e67f4c7-eb00-4fb6-8af4-0a732f6b974f

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
theorem _root_.solution {t : ℕ} (n : Fin t → ℕ) (c : ℤ) (j : Fin t) :
    numPt (Function.update n j (n j + 1)) c = numPt n c + Pi.single j.castSucc 1 := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [numPt, (Fin.castSucc_ne_last j).symm]
  | cast i =>
    by_cases h : i = j
    · subst h; simp [numPt]
    · simp [numPt, h, Function.update_apply]
end GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
