-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMeetNull_proof_2706e04a8a9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:46.249587+00:00
-- url     : https://prove2.me/submissions/e06315b8-dc6a-49a6-90aa-a3e4c46d452a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMeetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMeetNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMeetNull_null_of_mem_not_mem_360c3fd12496

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
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeMeetNull
theorem _root_.solution (hZ : ZeroLocusDimH.Statement) : ConeMeetNull.Statement := by
  intro n e h W W' hWp hW'p hne hW hW'
  by_cases hle : W' ≤ W
  ·
    have hnle : ¬ W ≤ W' := fun h' => hne (le_antisymm h' hle)
    obtain ⟨g, hgW, hgW'⟩ := Set.not_subset.mp hnle
    rw [Set.inter_comm]
    exact ConeMeetNull.null_of_mem_not_mem hZ h W' W hW' g hgW hgW'
  · obtain ⟨g, hgW', hgW⟩ := Set.not_subset.mp hle
    exact ConeMeetNull.null_of_mem_not_mem hZ h W W' hW g hgW' hgW
end ConeMeetNull
end GroundTheory.Heights₂.Heights
