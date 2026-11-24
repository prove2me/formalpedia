-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_mem_wwIdeal_of_aeval_eq_zero_25b295e2b105
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:42.835527+00:00
-- url     : https://prove2.me/submissions/1821e926-9876-4181-9694-3487600ee8ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_not_mem_ker_iff_aeval_ne_69965e549228


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
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) {s : MRing (T.wwIdx ι ν κ)} {β : T.WBlk → ℕ} (hs : IsMultiHomog s β)
    (h : aeval (T.wwCoord x δ e φ a₀ a₁) s = 0) : s ∈ T.wwIdeal x δ e φ a₀ a₁ := by
  by_contra h'
  have h'' : s ∉ RingHom.ker (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁)) := h'
  exact ((DiagRAux.not_mem_ker_iff_aeval_ne _ s β hs).1 h'') h
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
