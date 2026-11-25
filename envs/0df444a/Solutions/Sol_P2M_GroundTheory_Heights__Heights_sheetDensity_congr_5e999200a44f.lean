-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sheetDensity_congr_5e999200a44f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:59.653568+00:00
-- url     : https://prove2.me/submissions/decd8cef-1ed4-4dc8-8125-eced9c23bae8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsIntegralProjIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartProjIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsIntegralProjIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero


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
open MeasureTheory Filter
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegralAt sheetDensity
  fibre pot mcPts fibreFinite isOpen_blockNonzero)
variable {K : Type*} [Fintype K] {ι : K → Type*} {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {g g' : ((Σ k, ι k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
  unfold sheetDensity
  split_ifs with hγ
  · have hs : IsSheet P Ψ y w hγ.choose := hγ.choose_spec
    rw [h _ hs.2.self_of_nhds.2.1]
  · rfl
end GroundTheory.Heights₂.Heights
