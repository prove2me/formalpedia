-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_analyticAt_of_eventually_differentiableAt_1dd9a6cb1b42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:48.009534+00:00
-- url     : https://prove2.me/submissions/81904193-b8d7-49dd-8ebf-43afd2333d37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSheetHessPSD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ComplexOrder
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {e : ℕ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') : AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp h
  rw [analyticAt_pi_iff]
  intro p
  exact osgood e U (fun y' => γ y' p) hUo
    (fun y' hy' => ((differentiableAt_pi.mp (hU y' hy')) p).differentiableWithinAt) y hyU
end GroundTheory.Heights₂.Heights.Inter
