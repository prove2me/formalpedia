-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_f9ef88b8fca0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:49.855018+00:00
-- url     : https://prove2.me/submissions/c8b32760-6db2-48b8-8de1-045040428c02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StWWRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsAlgebraicMapAdjoin

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
open ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter
namespace RatioField
theorem _root_.solution [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {z : Ω} (hz : IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) z)
    {s : Set Φ} (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by
  let ψ := (algebraMap Ω Φ).toRatAlgHom
  have ht' : AlgebraicIndependent ℚ (ψ ∘ t) := ht.map' (algebraMap Ω Φ).injective
  have h4 : IsAlgebraic (Algebra.adjoin ℚ (Set.range (ψ ∘ t))) (ψ z) := by
    by_contra h
    have h3 : AlgebraicIndependent ℚ (fun o : Option (Fin d) => o.elim z t) := by
      refine AlgebraicIndependent.of_comp ψ ?_
      convert (ht'.option_iff_transcendental (ψ z)).mpr h using 1
      funext o
      cases o <;> rfl
    exact (ht.option_iff_transcendental z).mp h3 (IntermediateField.isAlgebraic_adjoin_iff.mp hz)
  have hsub : Set.range (ψ ∘ t) ⊆ s := by
    rintro _ ⟨n, rfl⟩
    exact hs n
  exact IntermediateField.isAlgebraic_adjoin_iff.mpr (h4.tower_top_of_subalgebra_le (Algebra.adjoin_mono hsub))
end RatioField
end GroundTheory.Heights₂.Heights.Inter
