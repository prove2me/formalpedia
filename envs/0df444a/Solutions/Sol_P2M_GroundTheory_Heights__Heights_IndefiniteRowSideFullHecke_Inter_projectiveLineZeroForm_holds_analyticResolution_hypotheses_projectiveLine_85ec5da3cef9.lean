-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projectiveLineZeroForm_holds_analyticResolution_hypotheses_projectiveLine_85ec5da3cef9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:00:08.594799+00:00
-- url     : https://prove2.me/submissions/34163e1a-1778-482e-80b6-80c8a9a73779

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineHomogeneousLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IfaceInh
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_holoMap_infty_2f5ab79e8182
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isHolomorphicSection
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSimpleNormalCrossing
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace projectiveLineZeroForm_holds
theorem _root_.solution :
    IsPotential ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ∧
    IsSection ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ReciprocityTheory.AnForm.M.projectiveLinePairSection ∧
    IsSNC ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ReciprocityTheory.AnForm.M.projectiveLinePairSection ![1]
      ![({OnePoint.infty} : Set (OnePoint ℂ))] ∧
    HoloMap (ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))) ReciprocityTheory.AnForm.M.p1
      Subtype.val ∧
    ReciprocityTheory.AnForm.M.p1.Smooth ReciprocityTheory.AnForm.M.fsH ∧
    ∀ i : Fin 0, IsPotential ReciprocityTheory.AnForm.M.p1 ((Fin.elim0 : Fin 0 → LocPot (OnePoint ℂ)) i) :=
  ⟨ReciprocityTheory.AnForm.M.projLine_isSmoothPotential, ReciprocityTheory.AnForm.M.projLine_isHolomorphicSection, ReciprocityTheory.AnForm.M.projLine_isSimpleNormalCrossing,
    holoMap_infty, ReciprocityTheory.AnForm.M.projLine_smooth_of_charts ReciprocityTheory.AnForm.M.contDiff_fubiniStudyRatio_comp_chart0
      ReciprocityTheory.AnForm.M.contDiff_fubiniStudyRatio_comp_chart1, fun i => i.elim0⟩
end projectiveLineZeroForm_holds
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
