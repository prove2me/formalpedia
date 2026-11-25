-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoordRing_map_405f3101cff5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:03.008521+00:00
-- url     : https://prove2.me/submissions/10d289ce-f732-4a98-a3ed-0beb0e75e27e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTruncSpecialize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) (p : Σ o, bundleIdx ι M o) :
    g (projCoordRing y w φ u p) = projCoordRing y w φ (g ∘ u) p := by
  rcases p with ⟨_ | k, l⟩ <;> simp [projCoordRing, map_sum]
end GroundTheory.Heights₂.Heights.NumbersDVR
