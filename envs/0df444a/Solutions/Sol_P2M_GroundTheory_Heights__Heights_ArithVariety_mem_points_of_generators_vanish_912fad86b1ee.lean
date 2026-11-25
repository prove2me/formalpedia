-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_of_generators_vanish_912fad86b1ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:18.137014+00:00
-- url     : https://prove2.me/submissions/fb29023e-37d8-4dbc-bcdd-0691f60be3e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MemPointsOfGeneratorsVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights
namespace ArithVariety
theorem _root_.solution (P : ArithVariety n) {r : ℕ}
    {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ} (hG : P.IsHomogGenerators G δ)
    {z : Cone n ℂ} (hz : BlockNonzero z) (h0 : ∀ i, evalCone z (G i) = 0) : z ∈ P.points ℂ := by
  refine ⟨hz, fun f hf ↦ ?_⟩
  rw [← hG.span_eq] at hf
  have hle : Ideal.span (Set.range G) ≤
      RingHom.ker (eval₂Hom (Int.castRingHom ℂ) fun v : Coord n ↦ z v.1 v.2) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact h0 i
  exact hle hf
end ArithVariety
end GroundTheory.Heights₂.Heights
