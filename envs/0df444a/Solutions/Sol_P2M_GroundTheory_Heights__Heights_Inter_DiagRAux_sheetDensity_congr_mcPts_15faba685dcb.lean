-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_sheetDensity_congr_mcPts_15faba685dcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:56:45.175281+00:00
-- url     : https://prove2.me/submissions/cbb3f2d2-f196-4cf3-a4d9-9032f21e9cb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_maDensity_congr_of_eventuallyEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z)
    (hg : ∀ z ∈ mcPts P, g z = g' z) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ' g' y w := by
  unfold sheetDensity
  split_ifs with hγ
  · have hev := hγ.choose_spec.2
    have hy : hγ.choose y ∈ mcPts P := hev.self_of_nhds.2.1
    rw [hg _ hy]
    congr 1
    apply maDensity_congr_of_eventuallyEq
    intro j
    filter_upwards [hev] with y' hy' using hφ j _ hy'.2.1
  · rfl
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
