-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:22:08.960536+00:00
-- url     : https://prove2.me/submissions/165a2e81-956c-4ad7-8f14-fc2778aba6b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
namespace PIW.AdelicOrbitU
theorem _root_.solution [CharZero F] {θ : E} (hθ0 : θ ≠ 0) (hσθ : σ θ = -θ) :
    LinearIndependent F ![(1 : E), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h' : s • (1 : E) - t • θ = 0 := by
    have := congrArg σ hst
    simp only [map_add, map_smul, map_one, hσθ, smul_neg, map_zero] at this
    linear_combination this
  have h3 : t • θ + t • θ = 0 := by linear_combination hst - h'
  have ht : t = 0 := by
    have h4 : (2 * t) • θ = 0 := by rw [two_mul, add_smul]; exact h3
    rcases smul_eq_zero.mp h4 with h | h
    · simpa using h
    · exact absurd h hθ0
  subst ht
  refine ⟨?_, rfl⟩
  simpa using hst
end PIW.AdelicOrbitU
