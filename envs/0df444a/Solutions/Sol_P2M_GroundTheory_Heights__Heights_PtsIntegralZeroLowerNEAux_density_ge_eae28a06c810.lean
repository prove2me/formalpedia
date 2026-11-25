-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_density_ge_eae28a06c810
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:33.20497+00:00
-- url     : https://prove2.me/submissions/dbffb5db-e281-4987-b036-02bbfc4e3d1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPtsIntegralZeroLowerNE
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_maDensity_zero_2fd3328216c0

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
theorem _root_.solution {W : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ} {g : ((Σ k, ι k) → ℂ) → ℝ} {c : ℝ}
    (hc : ∀ z ∈ mcPts W, c ≤ g z) {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre W Ψ y) :
    c ≤ sheetDensity W Ψ φ g y w := by
  classical
  obtain ⟨z, hz, rfl, hΨz⟩ := hw
  have hex : ∃ γ, IsSheet W Ψ y (segre z) γ :=
    ⟨fun _ => z, rfl, Filter.Eventually.of_forall fun y' =>
      ⟨differentiableAt_const _, hz, by rw [Subsingleton.elim y' y]; exact hΨz⟩⟩
  unfold sheetDensity
  rw [dif_pos hex, maDensity_zero, mul_one]
  exact hc _ hex.choose_spec.2.self_of_nhds.2.1
end GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
