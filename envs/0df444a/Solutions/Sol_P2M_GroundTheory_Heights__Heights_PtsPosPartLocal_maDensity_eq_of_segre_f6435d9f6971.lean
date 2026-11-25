-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_eq_of_segre_f6435d9f6971
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:41.246822+00:00
-- url     : https://prove2.me/submissions/fb1a77ec-b81a-48cc-b5bb-9fe071b5691f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_bsmul_f913413ea179
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eq_bsmul_of_segre_eq


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
theorem _root_.solution {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    maDensity (fun j y' => pot L j (γ' y')) y = maDensity (fun j y' => pot L j (γ y')) y := by
  choose i0 hi0 using hy
  have hcont : ∀ᶠ y' in 𝓝 y, ∀ k, γ y' ⟨k, i0 k⟩ ≠ 0 :=
    eventually_all.mpr fun k => (analyticAt_coord hγ ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  refine maDensity_bsmul (c := fun k y' => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩) hL hγ
    (fun k => ⟨i0 k, hi0 k⟩)
    (fun k => (analyticAt_coord hγ' ⟨k, i0 k⟩).div (analyticAt_coord hγ ⟨k, i0 k⟩) (hi0 k))
    (fun k => div_ne_zero ((eq_bsmul_of_segre_eq i0 hi0 hseg.eq_of_nhds).1 k) (hi0 k)) ?_
  filter_upwards [hcont, hseg] with y' h1 h2
  exact (eq_bsmul_of_segre_eq i0 h1 h2).2
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
