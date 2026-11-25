-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_sheetDensity_eq_a10d7016cd98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:16:47.596421+00:00
-- url     : https://prove2.me/submissions/0e1f7cd3-8d9a-4df9-9f73-391731f47c19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPtsIntegralPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_of_segre


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G MeasureTheory
open GroundTheory.Heights₂.Heights.PtsIntegralPoints
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsIntegralPoints
theorem _root_.solution (P : Ideal (Geo.MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z)
    (y : Fin 0 → ℂ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ Geo.mcPts P)
    (hΨ : Ψ (Geo.segre z) = Fin.cons 1 y) :
    Geo.sheetDensity P Ψ Fin.elim0 g y (Geo.segre z) = g z := by
  have hex : ∃ γ, Geo.IsSheet P Ψ y (Geo.segre z) γ := by
    refine ⟨fun _ ↦ z, rfl, Filter.Eventually.of_forall fun y' ↦ ⟨differentiableAt_const _, hz, ?_⟩⟩
    rw [Subsingleton.elim y' y]
    exact hΨ
  rw [Geo.sheetDensity, dif_pos hex]
  obtain ⟨hseg, hev⟩ := hex.choose_spec
  have hmem : hex.choose y ∈ Geo.mcPts P := hev.self_of_nhds.2.1
  obtain ⟨c, hc, hcz⟩ := Geo.sameOrbit_of_segre (z := z) hmem.1 1 one_ne_zero (by rw [one_smul, hseg])
  have hgz : g z = g (hex.choose y) := (congrArg g hcz).trans (hg c _ hc hmem)
  rw [hgz]
  simp [Geo.maDensity, Geo.mixedDisc]
end GroundTheory.Heights₂.Heights.PtsIntegralPoints
