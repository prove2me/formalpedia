-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_lineVal_cross_520c123127dc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:22.568462+00:00
-- url     : https://prove2.me/submissions/754409be-eb6c-4175-be15-dc385ef15344

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
theorem _root_.solution {Φ : Type*} [Field Φ] [Algebra Ω Φ] (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) :
    T.lineVal e ψ a₀ * T.lineVal e ψ' a₁ - T.lineVal e ψ' a₀ * T.lineVal e ψ a₁ =
      algebraMap Ω Φ (ψ (e 0) * ψ' (e 1) - ψ' (e 0) * ψ (e 1)) * (a₁ - a₀) := by
  simp only [T.lineVal, map_sub, map_mul]
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
