-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_self_b948cf6b7db2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:40.357725+00:00
-- url     : https://prove2.me/submissions/cbdf3fb3-4035-45cf-accd-3e067482da4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_sum_norm_sq_3d58e7f47ece

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
theorem _root_.solution {p : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1) : coordAlong p p = 1 := by
  rw [coordAlong, ← ofReal_sum_norm_sq, hp, Complex.ofReal_one]
end GroundTheory.Heights₂.Heights.SphereProjectionLaw
