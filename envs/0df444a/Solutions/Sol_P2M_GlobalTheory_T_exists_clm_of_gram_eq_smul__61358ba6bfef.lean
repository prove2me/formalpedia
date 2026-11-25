-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_clm_of_gram_eq_smul__61358ba6bfef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:09.174554+00:00
-- url     : https://prove2.me/submissions/576816ec-3370-47a3-923b-c5bb59cc5733

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsClmOfGramEqSmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsClmOfGramEqSmulStatement
import Theorems.Thm_GlobalTheory_exists_clm_of_gram_eq_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E) (K : ℝ), (∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  first | exact @GlobalTheory.exists_clm_of_gram_eq_smul | exact GlobalTheory.exists_clm_of_gram_eq_smul | (intros; apply GlobalTheory.exists_clm_of_gram_eq_smul <;> assumption)
end _root_.GlobalTheory.T
