-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_unique_1911557ddd21
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:36.491075+00:00
-- url     : https://prove2.me/submissions/d88e8492-9e23-4406-ba25-4d919a5567dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension

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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {κ : Type*} [Unique κ] (w : κ → V) :
    det (gram ℂ w) = ((‖w default‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_unique, gram_apply, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
end GroundTheory.Heights₂.Heights
