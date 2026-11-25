-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_congr_7067f4d9748e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:52:39.0822+00:00
-- url     : https://prove2.me/submissions/c83b44ad-88e5-43fd-8f81-56952f8d58b6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
theorem _root_.solution (A : FinHolAtlas e X) {P Q : LocPot X} (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, ∀ z ∈ P.U x, P.φ x z = Q.φ x z) (hP : IsPotential A P) : IsPotential A Q := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · rw [← hU x]
    exact (hP.1 x j).congr fun t ht => (hφ x _ ht.2).symm
  · rw [← hU x, ← hU x'] at hy
    obtain ⟨W, hW, hyW, G, hG, hd⟩ := hP.2 x x' y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    rw [← hU x, ← hU x'] at hz
    rw [← hφ x z hz.1.2, ← hφ x' z hz.2, hd z hz]
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
