-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isRelevant_ptI_fd8c8e14f767
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:40.249158+00:00
-- url     : https://prove2.me/submissions/5ad26a8c-2b2a-494a-ac69-ed02a282ea09

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_X_not_mem_span_X_f2f34601db8d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fin_two_add_one_ne_0a1e6c3a7163
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {R : Type} [CommRing R] [Nontrivial R] (j : Fin 2) :
    IsRelevant (ptI (R := R) j) := by
  intro k
  refine ⟨j + 1, X_not_mem_span_X ?_⟩
  intro h
  have := congrArg Sigma.snd h
  exact fin_two_add_one_ne j (by simpa using this.symm)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
