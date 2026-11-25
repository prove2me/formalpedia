-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_holoMap_infty_2f5ab79e8182
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:11.634031+00:00
-- url     : https://prove2.me/submissions/96216aa0-e9a4-474f-a518-b32df6ad3dc8

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
theorem _root_.solution :
    HoloMap (ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))) ReciprocityTheory.AnForm.M.p1
      Subtype.val := by
  refine ⟨continuous_subtype_val, fun j k y _ => ?_⟩
  have hc : (ReciprocityTheory.AnForm.M.p1.chart k ∘ Subtype.val ∘
      ((ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))).chart j).symm) =
      fun _ => (ReciprocityTheory.AnForm.M.p1.chart k ∘ Subtype.val ∘
        ((ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))).chart j).symm) y :=
    funext fun y' => congrArg _ (Subsingleton.elim y' y)
  rw [hc]
  exact analyticAt_const
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
