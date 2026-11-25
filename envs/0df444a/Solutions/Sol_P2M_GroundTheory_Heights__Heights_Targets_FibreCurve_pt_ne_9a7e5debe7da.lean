-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_pt_ne_9a7e5debe7da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:17.763301+00:00
-- url     : https://prove2.me/submissions/af860a87-11a7-4315-b531-ee4a9c9a6d0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.FibreCurve
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.FibreCurve
theorem _root_.solution {u : Ω} (hu : u ≠ 0) (p : Σ k, B2 k) : pt u p ≠ 0 := by
  obtain ⟨k, i⟩ := p
  fin_cases k <;> fin_cases i <;> simp [pt, hu]
end GroundTheory.Heights₂.Heights.Targets.FibreCurve
