-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_dual_pair_2eb99c930643
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:19.02468+00:00
-- url     : https://prove2.me/submissions/c67c8a67-766a-41fc-8f16-5e1cdcbaa772

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_bounded_frame_c1f354ee7137

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0) (e : Module.Basis (Fin 2) Ω E) :
    ∃ ψ₀ ∈ T.dualLat B i, ∃ ψ₁ ∈ T.dualLat B i, ψ₀ (e 0) * ψ₁ (e 1) - ψ₁ (e 0) * ψ₀ (e 1) ≠ 0 := by
  obtain ⟨f, b, N, -, hf0, -, hN⟩ := exists_bounded_frame B i hi
  have hψ : ∀ q (v : E), (f ^ N • b.coord q) v = f ^ N * b.repr v q := fun q v => by
    simp [Module.Basis.coord_apply]
  refine ⟨f ^ N • b.coord 0, fun v hv => ?_, f ^ N • b.coord 1, fun v hv => ?_, ?_⟩
  · rw [hψ]; exact hN v hv 0
  · rw [hψ]; exact hN v hv 1
  · rw [hψ, hψ, hψ, hψ]
    have hdet := (b.isUnit_det e).ne_zero
    rw [Module.Basis.det_apply, Matrix.det_fin_two] at hdet
    simp only [Module.Basis.toMatrix_apply] at hdet
    have : f ^ N * b.repr (e 0) 0 * (f ^ N * b.repr (e 1) 1) - f ^ N * b.repr (e 0) 1 * (f ^ N * b.repr (e 1) 0) =
        (f ^ N) ^ 2 * (b.repr (e 0) 0 * b.repr (e 1) 1 - b.repr (e 1) 0 * b.repr (e 0) 1) := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hf0)) hdet
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
