-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanFubini_nrmGroups_consGroup_5b3e998146ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:50.591705+00:00
-- url     : https://prove2.me/submissions/ea9964aa-a3a5-4501-b8aa-189d5c81e251

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanFubini

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
open MeasureTheory Measure Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanFubini
namespace GroundTheory.Heights₂.Heights.SphereMeanFubini
theorem _root_.solution {n : ℕ} (h : HermNorm n) (k : ℕ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) :
    nrmGroups h (k + 1) (consGroup v w) = consGroup (nrmv h v) (nrmGroups h k w) := by
  funext ⟨i, j⟩
  cases i using Fin.cases <;> simp [nrmGroups, consGroup, nrmv]
end GroundTheory.Heights₂.Heights.SphereMeanFubini
