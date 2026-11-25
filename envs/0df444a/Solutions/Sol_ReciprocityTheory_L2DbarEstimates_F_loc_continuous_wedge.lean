-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_continuous_wedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:20:56.611912+00:00
-- url     : https://prove2.me/submissions/c5c02a2f-09c9-465a-a656-918e23f085a8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) :
    Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => wedge p.1 p.2) := by
  first
  | (unfold wedge; fun_prop)
  | (refine continuous_pi fun j => continuous_pi fun k => ?_
     unfold wedge
     fun_prop)
  | (refine continuous_pi fun j => continuous_pi fun k => ?_
     simp only [wedge]
     exact (((continuous_apply j).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)).sub
       (((continuous_apply k).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)))
end ReciprocityTheory.L2DbarEstimates.F
