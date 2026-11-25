-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagStaircaseOrbit_bijective_of_injective_5dfb25d50c40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:53.759752+00:00
-- url     : https://prove2.me/submissions/9bc61e5f-8997-4e01-bf9d-521e526f76bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagStaircaseOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagStaircaseOrbit
theorem _root_.solution {f N : ℕ} (γ : Fin f × Fin N →₀ ℕ) (τ : Fin f)
    (hlt : ∀ i, γ (τ, i) < N) (hinj : Function.Injective fun i : Fin N => γ (τ, i)) :
    Function.Bijective fun i : Fin N => (⟨γ (τ, i), hlt i⟩ : Fin N) := by
  refine Finite.injective_iff_bijective.mp ?_
  intro i j h
  exact hinj (congrArg Fin.val h)
end FlagStaircaseOrbit
end GroundTheory.Heights₂.Heights.RestTerms
