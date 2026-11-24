-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_sum_norm_sq_3d58e7f47ece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:54.923892+00:00
-- url     : https://prove2.me/submissions/7d5b208c-1751-4889-8044-215876f9eb47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_norm_sq_0f7fc2aa98eb

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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SphereProjectionLaw
theorem _root_.solution (v : Fin n → ℂ) :
    ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) = ∑ j, v j * star (v j) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ ↦ ofReal_norm_sq (v j)
end GroundTheory.Heights₂.Heights.SphereProjectionLaw
