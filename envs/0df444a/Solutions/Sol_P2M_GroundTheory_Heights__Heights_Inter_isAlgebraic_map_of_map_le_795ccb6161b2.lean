-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isAlgebraic_map_of_map_le_795ccb6161b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:33.18634+00:00
-- url     : https://prove2.me/submissions/898eade0-6c0d-4800-b17a-81638d7a10ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StYYRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PYYRatioBasis

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.T
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra ℚ Ω] [Algebra ℚ Φ]
    (f : Ω →ₐ[ℚ] Φ) {L : IntermediateField ℚ Ω} {M : IntermediateField ℚ Φ} (hLM : L.map f ≤ M) {y : Ω}
    (hy : IsAlgebraic L y) : IsAlgebraic M (f y) := by
  obtain ⟨p, hp, hpy⟩ := hy
  let ψ : L →+* M := ((f : Ω →+* Φ).comp (algebraMap L Ω)).codRestrict M (fun z => hLM ⟨z, z.2, rfl⟩)
  have hψ : (algebraMap M Φ).comp ψ = (f : Ω →+* Φ).comp (algebraMap L Ω) := by
    ext z; rfl
  refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff ψ.injective).mpr hp, ?_⟩
  have h := congrArg f hpy
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hψ]
  rw [Polynomial.aeval_def, map_zero] at h
  rw [← h]
  exact (Polynomial.hom_eval₂ p (algebraMap L Ω) (f : Ω →+* Φ) y).symm
end GroundTheory.Heights₂.Heights.Inter
