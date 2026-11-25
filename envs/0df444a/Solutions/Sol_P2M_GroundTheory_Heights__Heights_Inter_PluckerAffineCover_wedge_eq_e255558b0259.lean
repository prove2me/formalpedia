-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wedge_eq_e255558b0259
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:43.167712+00:00
-- url     : https://prove2.me/submissions/77b56630-112f-4862-817d-5a2fb67e07bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover

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
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω) (u w : E) :
    ψ u * ψ' w - ψ w * ψ' u = (ψ (e 0) * ψ' (e 1) - ψ (e 1) * ψ' (e 0)) * T.detE e u w := by
  have hv : ∀ (v : E) (χ : E →ₗ[Ω] Ω), χ v = e.repr v 0 * χ (e 0) + e.repr v 1 * χ (e 1) := by
    intro v χ
    have h := e.sum_repr v
    rw [Fin.sum_univ_two] at h
    calc χ v = χ (e.repr v 0 • e 0 + e.repr v 1 • e 1) := by rw [h]
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  rw [hv u ψ, hv u ψ', hv w ψ, hv w ψ']
  unfold T.detE
  ring
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
