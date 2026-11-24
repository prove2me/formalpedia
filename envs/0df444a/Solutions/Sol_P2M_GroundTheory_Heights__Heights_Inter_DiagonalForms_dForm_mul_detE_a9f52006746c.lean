-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_mul_detE_a9f52006746c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:22.088847+00:00
-- url     : https://prove2.me/submissions/1d9ebbeb-4cae-416d-a583-534c99cac222

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms

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
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω) (u w : E) :
    (ψ (e 0) * ψ' (e 1) - ψ' (e 0) * ψ (e 1)) * T.detE e u w = ψ u * ψ' w - ψ w * ψ' u := by
  have hx : ∀ (χ : E →ₗ[Ω] Ω) (v : E), χ v = e.repr v 0 * χ (e 0) + e.repr v 1 * χ (e 1) := by
    intro χ v
    have h := congrArg χ (e.sum_repr v)
    rw [map_sum, Fin.sum_univ_two, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    exact h.symm
  rw [hx ψ u, hx ψ' w, hx ψ w, hx ψ' u]
  simp only [T.detE]
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
