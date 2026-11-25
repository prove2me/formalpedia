-- Prove2me | solution 1 for PositivityTheory.KReal.graph_orth_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:43.374806+00:00
-- url     : https://prove2.me/submissions/4bab326c-3c1d-4b98-95d8-eabffb086f07

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {p q : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    (ρ : Mat p q →ₗ[ℂ] Module.End ℂ A) (aA : AdjG ρ) (K : Submodule ℂ A) (hK : ∀ W, ∀ v ∈ K, ρ W v ∈ K) :
    ∀ W, ∀ u ∈ Kᗮ, ρ W u ∈ Kᗮ := by
  intro W u hu
  rw [Submodule.mem_orthogonal']
  intro v hv
  have hu' := (Submodule.mem_orthogonal' K u).1 hu
  rw [Matrix.matrix_eq_sum_single W]
  simp only [map_sum, LinearMap.sum_apply, sum_inner]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have hs : Matrix.single a b (W a b) = W a b • Eab a b := by
    simp [Eab, Matrix.smul_single]
  rw [hs, map_smul, LinearMap.smul_apply, inner_smul_left, aA, hu' _ (hK _ _ hv), mul_zero, mul_zero]
end PositivityTheory.KReal
