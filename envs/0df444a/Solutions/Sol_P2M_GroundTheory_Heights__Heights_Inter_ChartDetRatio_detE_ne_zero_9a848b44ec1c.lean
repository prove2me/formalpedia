-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_detE_ne_zero_9a848b44ec1c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:59.94974+00:00
-- url     : https://prove2.me/submissions/0075b346-f750-4c70-9cf4-cbf7d00511d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartDetRatio
theorem _root_.solution {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) : T.detE e (b 0) (b 1) ≠ 0 := by
  have hu : IsUnit (e.det b) := (Module.Basis.is_basis_iff_det e).1 ⟨hli, hsp⟩
  have h : e.det b = T.detE e (b 0) (b 1) := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp only [Module.Basis.toMatrix_apply, T.detE]
    ring
  rw [← h]
  exact hu.ne_zero
end ChartDetRatio
end GroundTheory.Heights₂.Heights.Inter
