-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSmall_eval_map_int_f9e852c2cdf5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:09.9209+00:00
-- url     : https://prove2.me/submissions/868a3325-e71a-483a-a8e9-640c4daff55d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.YPlusSmall
theorem _root_.solution {σ : Type*} (z : σ → ℂ) (F : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) F) = aeval z F := by
  rw [eval_map, aeval_def, algebraMap_int_eq]
end GroundTheory.Heights₂.Heights.YPlusSmall
