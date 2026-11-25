-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_congr_ae707927fd3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:00.810483+00:00
-- url     : https://prove2.me/submissions/8376b91f-6854-48e8-88d4-06f51cb39e1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassPos
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjPotMassPos
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X]
    {A : FinHolAtlas e X} {P Q : LocPot X} (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, ∀ z ∈ P.U x, P.φ x z = Q.φ x z) (hP : IsPotential A P) : IsPotential A Q := by
  obtain ⟨hs, hd⟩ := hP
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have h := hs x j
    rw [hU x] at h
    refine h.congr fun w hw => ?_
    simp only [Function.comp_apply]
    exact (hφ x _ ((hU x).symm ▸ hw.2)).symm
  · rw [← hU x, ← hU x'] at hy
    obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hd x x' y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    rw [← hU x, ← hU x'] at hz
    rw [← hφ x z hz.1.2, ← hφ x' z hz.2]
    exact hGe z hz
end ProjPotMassPos
end GroundTheory.Heights₂.Heights.Targets
