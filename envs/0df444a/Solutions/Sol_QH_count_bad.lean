-- Prove2me | solution 1 for QH.count_bad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:55.102484+00:00
-- url     : https://prove2.me/submissions/74b6d57d-11a1-417a-ae72-0f542aff6bf1

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZAll
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_CountBadCore
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_CountBad
import Theorems.Thm_QH_count_bad_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∃ C : ℝ, ∀ (Q F : ℝ) (B : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ B, q.Prime ∧ F < q ∧ ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox Q ψ) → (B.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  obtain ⟨C, -, hC⟩ := count_bad_core
  refine ⟨C, fun Q F B hQ hB => hC Q F B hQ fun q hq => ?_⟩
  obtain ⟨hp, hF, f, hne, ψ, hf, hN, hψ, hz⟩ := hB q hq
  exact ⟨hp, hF, f * q, f, hne, ψ, rfl, hf, hψ, hN, hz⟩
end QH
