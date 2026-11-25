-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_pow_descent_cyclotomic__912ff4c996ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:33:53.712251+00:00
-- url     : https://prove2.me/submissions/9edc6448-aa50-4cf8-9768-dfb0c7c67a54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowDescentCyclotomic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowDescentCyclotomicStatement
import Theorems.Thm_GlobalTheory_exists_pow_descent_cyclotomic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u → ∃ v : E, v ^ (l ^ r) = u := by
  first | exact @GlobalTheory.exists_pow_descent_cyclotomic | exact GlobalTheory.exists_pow_descent_cyclotomic | (intros; apply GlobalTheory.exists_pow_descent_cyclotomic <;> assumption)
end _root_.GlobalTheory.T
