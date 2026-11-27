-- Prove2me | solution 1 for P2M_GlobalTheory_T_hasSum_graded_of_mul_degree__c02842eb4fa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:24.647668+00:00
-- url     : https://prove2.me/submissions/671298f6-8b43-44a2-80ad-98c4af173df7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumGradedOfMulDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumGradedOfMulDegreeStatement
import Theorems.Thm_GlobalTheory_hasSum_graded_of_mul_degree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) [AddCommGroup X] (Rel : ℕ → (X → C) → C → Prop) (n k : ℕ), 1 ≤ n → 1 ≤ k → (∀ (l l' : ℕ) (a a' : X → C) (c c' : C), 1 ≤ l → 1 ≤ l' → Rel l a c → Rel l' a' c' → ∃ a'', Rel (l + l') a'' (c * c') ∧ ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) → (∃ κ : C, κ ≠ 0 ∧ ∀ a c, Rel (n * k) a c → HasSum a (κ * c)) → ∃ u : C, u ≠ 0 ∧ ∀ a c, Rel k a c → Summable a → HasSum a (u * c) := by
  first | exact @GlobalTheory.hasSum_graded_of_mul_degree | exact GlobalTheory.hasSum_graded_of_mul_degree | (intros; apply GlobalTheory.hasSum_graded_of_mul_degree <;> assumption)
end _root_.GlobalTheory.T
