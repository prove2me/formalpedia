-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_log_fs_eq_std_2b91042fd6ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:59.826797+00:00
-- url     : https://prove2.me/submissions/3a57576a-0aae-43a3-b6b0-e42e3f5679aa

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogNormGradDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogNormGradDensNonneg
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LogNormGradDensNonneg
namespace GroundTheory.Heights₂.Heights.LogNormGradDensNonneg
theorem _root_.solution (n : ℕ) :
    (fun z : Fin n → ℂ => Real.log ((ReciprocityTheory.ChartRestriction.G.Geo.fsMetric (Fin n)).ρ z)) =
      fun z => Real.log ((HermNorm.std n).dualNorm z) := by
  funext z
  simp [ReciprocityTheory.ChartRestriction.G.Geo.fsMetric, HermNorm.dualNorm, HermNorm.std, EuclideanSpace.norm_eq]
end GroundTheory.Heights₂.Heights.LogNormGradDensNonneg
