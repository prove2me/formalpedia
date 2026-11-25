-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_algebraMap_sub_eq_sum_conjugates__8f225b3c9a0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:42:22.561689+00:00
-- url     : https://prove2.me/submissions/7c27ed02-fb1a-4535-aa50-4246a12fb3da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlgebraMapSubEqSumConjugates
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlgebraMapSubEqSumConjugatesStatement
import Theorems.Thm_GlobalTheory_exists_algebraMap_sub_eq_sum_conjugates


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (y : Ω), ∃ (e : E) (s : Finset Ω), (∀ x ∈ s, x ≠ y ∧ ∃ σ : G E Ω, σ y = x) ∧ algebraMap E Ω e - y = ∑ x ∈ s, x := by
  first | exact @GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates | exact GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates | (intros; apply GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates <;> assumption)
end _root_.GlobalTheory.T
