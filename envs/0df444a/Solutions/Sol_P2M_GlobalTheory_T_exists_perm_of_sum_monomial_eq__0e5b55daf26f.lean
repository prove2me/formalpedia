-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_perm_of_sum_monomial_eq__0e5b55daf26f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:33:51.90312+00:00
-- url     : https://prove2.me/submissions/08a05198-2760-4241-8ced-f7241e05c768

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPermOfSumMonomialEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPermOfSumMonomialEqStatement
import Theorems.Thm_GlobalTheory_QFam_exists_perm_of_sum_monomial_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ), (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) → ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  first | exact @GlobalTheory.QFam.exists_perm_of_sum_monomial_eq | exact GlobalTheory.QFam.exists_perm_of_sum_monomial_eq | (intros; apply GlobalTheory.QFam.exists_perm_of_sum_monomial_eq <;> assumption)
end _root_.GlobalTheory.T
