-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_thetaOmega_p1Data_pot_631a1bd82bf8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:17:05.465518+00:00
-- url     : https://prove2.me/submissions/1f6ee5e3-d8f2-4a22-ba88-cf395530f732

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialAdd
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
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
theorem _root_.solution : IsPotential p1 (thetaOmega projLineChartData) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd p1 _ _
    (ReciprocityTheory.AnForm.M.isPotential_ofFun p1 0 fun _ => contDiffOn_const) projLine_isSmoothPotential
end GroundTheory.Heights₂.Heights.AnalyticLimit
