-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.dc_aeval_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:15.121398+00:00
-- url     : https://prove2.me/submissions/2c12403a-ff2d-42cc-919b-5d06b94e60d6

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
import Theorems.Thm_Bl_PowerApplication_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (p : ℂ[X]) :
    aeval T p f = p.eval z • f := by
  first | exact Bl.PowerApplication.goal1 .. | (apply Bl.PowerApplication.goal1 <;> assumption) | (intros; apply Bl.PowerApplication.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.DS
