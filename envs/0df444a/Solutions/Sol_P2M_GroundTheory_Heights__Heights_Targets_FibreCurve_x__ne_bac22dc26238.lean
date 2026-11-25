-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x__ne_bac22dc26238
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:40.061041+00:00
-- url     : https://prove2.me/submissions/24c6b719-d9da-4dea-aa9e-78a14e74c80f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_X_not_mem_564c8277a492

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.FibreCurve
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.FibreCurve
theorem _root_.solution {u : Ω} (hu : u ≠ 0) (p : Σ k, B2 k) : (gen u).x' p ≠ 0 := fun h =>
  X_not_mem hu p (by rw [← (gen u).genericFibre_ker_target, RingHom.mem_ker, aeval_X]; exact h)
end GroundTheory.Heights₂.Heights.Targets.FibreCurve
