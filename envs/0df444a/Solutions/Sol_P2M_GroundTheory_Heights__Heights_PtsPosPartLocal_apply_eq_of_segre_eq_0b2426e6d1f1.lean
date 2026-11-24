-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_apply_eq_of_segre_eq_0b2426e6d1f1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:50.641282+00:00
-- url     : https://prove2.me/submissions/4689f097-675f-494f-b40a-20bef3f6ed3e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
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
theorem _root_.solution {β : Sort*} {F : ((Σ k, ι k) → ℂ) → β}
    (hF : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → F (fun p => c p.1 * z p) = F z)
    {u v : (Σ k, ι k) → ℂ} (hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0) (h : segre u = segre v) : F v = F u := by
  choose i0 hi0 using hu
  obtain ⟨h1, h2⟩ := eq_bsmul_of_segre_eq i0 hi0 h
  calc F v = F (bsmul (fun k => v ⟨k, i0 k⟩ / u ⟨k, i0 k⟩) u) := congrArg F h2
    _ = F u := hF _ u fun k => div_ne_zero (h1 k) (hi0 k)
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
