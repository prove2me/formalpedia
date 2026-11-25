-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoord_eq_projCoordRing_f401ac45dd71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:30.356027+00:00
-- url     : https://prove2.me/submissions/b2e5c838-8748-4191-b1e2-17a74f88b05b

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
theorem _root_.solution {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    projCoord y w φ t = projCoordRing y w φ t := by
  funext p
  rcases p with ⟨_ | k, l⟩ <;> rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
