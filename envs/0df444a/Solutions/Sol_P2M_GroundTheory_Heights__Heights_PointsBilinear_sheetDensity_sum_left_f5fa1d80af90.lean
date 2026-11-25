-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_left_f5fa1d80af90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:27.243843+00:00
-- url     : https://prove2.me/submissions/d2b6fba6-d5cf-452d-b1e5-39bdd4789a19

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear

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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PointsBilinear
theorem _root_.solution {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (φ : Fin n → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type} [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin n → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ t, u t z) y w = ∑ t, sheetDensity P Ψ φ (u t) y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h, Finset.sum_mul]
  · simp only [dif_neg h, Finset.sum_const_zero]
end GroundTheory.Heights₂.Heights.PointsBilinear
