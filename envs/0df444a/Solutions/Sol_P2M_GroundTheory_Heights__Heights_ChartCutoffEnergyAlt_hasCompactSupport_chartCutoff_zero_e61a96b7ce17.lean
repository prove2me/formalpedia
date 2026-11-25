-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_hasCompactSupport_chartCutoff_zero_e61a96b7ce17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:35.842649+00:00
-- url     : https://prove2.me/submissions/a7538022-4a6d-45ab-957f-a6a3fbcbc666

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_chartCutoff_zero_eq_1b604a4b9efd

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
namespace GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
theorem _root_.solution {D : ℕ} :
    HasCompactSupport (chartCutoff 0 : (Fin D → ℂ) → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) 2) fun x hx => ?_
  rw [chartCutoff_zero_eq]
  apply Real.smoothTransition.zero_of_nonpos
  obtain ⟨i, hi⟩ : ∃ i, 2 < ‖x i‖ := by
    by_contra h
    push Not at h
    exact hx (mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr h))
  have : ‖x i‖ ^ 2 ≤ sqn x :=
    Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  nlinarith
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
