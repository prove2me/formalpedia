-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_boundedNonnegForm_83dddc37c4cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:24.973249+00:00
-- url     : https://prove2.me/submissions/2cf7333e-96df-4c68-9fb1-f5816e9bdfc0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isPlurisubharmonic
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSmoothPotential


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ThGe ell errE)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData projLine_fubiniStudy_isPosPot)
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution : IsBoundedNonnegForm p1 fsPot fsPot 1 :=
  ⟨projLine_isSmoothPotential, fun x k y hy w => projLine_isPlurisubharmonic x k y ⟨hy.1, hy.2.2⟩ w,
    fun _ _ _ _ _ => le_rfl⟩
end GroundTheory.Heights₂.Heights.AnalyticLimit
