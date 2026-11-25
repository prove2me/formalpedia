-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_analyticOnNhd_of_diffOn_dfa8683cecfc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:00.902395+00:00
-- url     : https://prove2.me/submissions/d0cb78b5-a087-4b8e-8172-fc3288bbeeb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
namespace GroundTheory.Heights₂.Heights.PtsPosPartLocal
theorem _root_.solution {m : ℕ} {σ : Type*} [Fintype σ] {U : Set (Fin m → ℂ)}
    {f : (Fin m → ℂ) → σ → ℂ} (hU : IsOpen U) (hf : ∀ y ∈ U, DifferentiableAt ℂ f y) :
    AnalyticOnNhd ℂ f U := fun y hy =>
  analyticAt_pi_iff.mpr fun i => osgood m U (fun y => f y i) hU
    (fun y' hy' => (differentiableAt_pi.mp (hf y' hy') i).differentiableWithinAt) y hy
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
