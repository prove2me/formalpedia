-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_77d7baeecfd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:48.536831+00:00
-- url     : https://prove2.me/submissions/a67f8abc-7923-4f78-af34-39a8db875833

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (H : ArchData K n) (δ : ℕ) (g : MvPolynomial (Fin 0 × Fin n) K) :
    chowHt H 0 δ g = chowHt H 0 0 g := by
  simp [chowHt]
end GroundTheory.Heights₂.Heights
