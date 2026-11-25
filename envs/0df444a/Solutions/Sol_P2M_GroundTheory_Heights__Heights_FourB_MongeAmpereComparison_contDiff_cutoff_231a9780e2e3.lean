-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_contDiff_cutoff_231a9780e2e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:30.730051+00:00
-- url     : https://prove2.me/submissions/3c190913-8dbe-43f2-8b75-b61eaf5c48df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hasDerivAt_cutoff_d9e21ca0833b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
theorem _root_.solution : ContDiff ℝ ∞ cutoff := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_cutoff t).differentiableAt, ?_⟩
  have : deriv cutoff = Real.smoothTransition := funext fun t => (hasDerivAt_cutoff t).deriv
  rw [this]
  exact Real.smoothTransition.contDiff (n := ⊤)
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
