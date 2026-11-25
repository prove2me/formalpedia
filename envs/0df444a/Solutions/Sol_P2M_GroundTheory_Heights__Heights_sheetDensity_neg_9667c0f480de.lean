-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sheetDensity_neg_9667c0f480de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:50.150092+00:00
-- url     : https://prove2.me/submissions/57f1be68-d4f0-4579-9cb7-93d59d4279bd

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
theorem _root_.solution (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs <;> simp [neg_mul]
end GroundTheory.Heights₂.Heights
