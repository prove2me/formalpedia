-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_detE_ne_ee895c1b2f58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:33:59.649248+00:00
-- url     : https://prove2.me/submissions/6d8f03b0-fd8f-4b56-b321-05c1f841f7b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_bounded_frame_c1f354ee7137
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_eq_det_fd6fff7a991a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_smul_3451d0035f0c

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
    ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, T.detE e u w ≠ 0 := by
  obtain ⟨f, b, -, -, hf0, hb, -⟩ := exists_bounded_frame B i hi
  obtain ⟨n₀, h₀⟩ := hb 0
  obtain ⟨n₁, h₁⟩ := hb 1
  refine ⟨_, h₀, _, h₁, ?_⟩
  rw [detE_smul, detE_eq_det]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf0)) (e.isUnit_det b).ne_zero
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
