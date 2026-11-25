-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projFirstCoord_segre_lift_ne_zero_589e025e7757
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:20.700179+00:00
-- url     : https://prove2.me/submissions/efa05c85-54aa-4a26-8044-2555fc783570

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_KerEqBotOfCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsPushForwardOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_DivPushResSideInhabitants
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjRegular
theorem _root_.solution :
    ∀ x ∈ ProjRegular.pointV, ProjRegular.projFirstCoordinate (segre (ProjectiveLineResolution.res.lift x x)) ≠ 0 := by
  intro x hx
  obtain rfl : x = ((0 : ℂ) : OnePoint ℂ) := hx
  intro h
  have h0 := congrFun h 0
  change ProjRegular.projFirstCoordinate (segre (ProjectiveLineResolution.lift ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ))) 0
    = 0 at h0
  rw [ProjectiveLineResolution.lift_coe] at h0
  simp [ProjRegular.projFirstCoordinate, segre] at h0
end ProjRegular
end GroundTheory.Heights₂.Heights.Targets
