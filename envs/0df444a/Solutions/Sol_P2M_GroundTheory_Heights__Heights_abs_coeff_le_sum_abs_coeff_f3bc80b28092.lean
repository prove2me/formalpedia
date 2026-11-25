-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_abs_coeff_le_sum_abs_coeff_f3bc80b28092
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:37.809801+00:00
-- url     : https://prove2.me/submissions/e87574d4-3684-413d-b24b-a2c18ee46876

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymStability

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {σ : Type*} (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |coeff m p| ≤ ∑ m' ∈ p.support, |coeff m' p| := by
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m' => |coeff m' p|) (fun _ _ => abs_nonneg _) hm
  · rw [notMem_support_iff.1 hm, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
end GroundTheory.Heights₂.Heights
