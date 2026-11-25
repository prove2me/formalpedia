-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffMinor_map_comp_subst_dde6ca6167d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:56.248187+00:00
-- url     : https://prove2.me/submissions/57185846-567a-4e8e-8f44-d23d03b8e461

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffMinor

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
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
omit [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) :
    (Polynomial.mapRingHom (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁))).comp
        (eval₂Hom (Int.castRingHom _) (lineSubst ι ν κ)) =
      (eval₂Hom (Polynomial.C.comp C) (blockSubst (Φ := Φ))).comp
        (T.multiConeMap (T.wwCoord x δ e φ a₀ a₀)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [T.multiConeMap]
  · rintro ⟨b, q⟩
    cases b <;> simp [T.multiConeMap, T.wwCoord, lineSubst, blockSubst]
    ring
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffMinor
