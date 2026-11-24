-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_norm_sq_0f7fc2aa98eb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:44.570971+00:00
-- url     : https://prove2.me/submissions/0da91c4b-0e88-4390-adc6-6a2154ad4045

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw

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
theorem _root_.solution (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * star x := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
end GroundTheory.Heights₂.Heights.SphereProjectionLaw
