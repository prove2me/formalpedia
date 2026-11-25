-- Prove2me | solution 1 for PI.WhitFunctDualWork.stable_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:34.713153+00:00
-- url     : https://prove2.me/submissions/147b9bf5-b98c-41e2-8bed-598be19eba58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WhitFunctDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WhittakerFunctionalDual_StableOfIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WhitFunctDualWork
open Formalism.L2.SG.GGMirabolic
namespace PI.WhitFunctDualWork
theorem _root_.solution {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, π g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  have := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    show (⊥ : Submodule ℂ V) = ⊤
    ext x
    simp [Subsingleton.elim x 0]
  · rcases IsSimpleOrder.eq_bot_or_eq_top
        (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation π) with h1 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)
end PI.WhitFunctDualWork
