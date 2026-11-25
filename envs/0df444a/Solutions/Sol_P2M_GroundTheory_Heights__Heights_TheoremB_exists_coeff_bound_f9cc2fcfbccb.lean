-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_exists_coeff_bound_f9cc2fcfbccb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:32.002224+00:00
-- url     : https://prove2.me/submissions/39ece5a3-94f0-4f98-a8c2-0dec19c899b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution {σ : Type*} (P : MvPolynomial σ ℝ) : ∃ M : ℝ, ∀ m, |coeff m P| ≤ M := by
  refine ⟨∑ m ∈ P.support, |coeff m P|, fun m => ?_⟩
  by_cases hm : m ∈ P.support
  · exact Finset.single_le_sum (f := fun m => |coeff m P|) (fun _ _ => abs_nonneg _) hm
  · rw [notMem_support_iff.1 hm, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
end GroundTheory.Heights₂.Heights.TheoremB
