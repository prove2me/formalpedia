-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_add_const_f7132524e540
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:22.236362+00:00
-- url     : https://prove2.me/submissions/40093f99-372e-4cd6-bc69-c626b85da4d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
theorem _root_.solution {ι : Type*} [Fintype ι] (f : (ι → ℂ) → ℝ) (c : ℝ) (z w : ι → ℂ) :
    levi (fun y => f y + c) z w = levi f z w := by
  have : fderiv ℝ (fun y => f y + c) = fderiv ℝ f := funext fun _ => fderiv_add_const c
  simp only [levi, this]
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
