-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_separating_basicOpen_functions__3526d83d5c45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:13.919729+00:00
-- url     : https://prove2.me/submissions/8a57abb2-e468-45fe-ae70-8fafdb19bb51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparatingBasicOpenFunctions
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparatingBasicOpenFunctionsStatement
import Theorems.Thm_GlobalTheory_exists_separating_basicOpen_functions


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  first | exact @GlobalTheory.exists_separating_basicOpen_functions | exact GlobalTheory.exists_separating_basicOpen_functions | (intros; apply GlobalTheory.exists_separating_basicOpen_functions <;> assumption)
end _root_.GlobalTheory.T
