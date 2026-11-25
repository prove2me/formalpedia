-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_monomial_ab5dd46129ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:54.735296+00:00
-- url     : https://prove2.me/submissions/a29807bd-0038-454b-ae02-670f982fcac3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution (T : Finset K) (d : (Σ k, ι k) →₀ ℕ) (c : F) :
    killBlocks T (monomial d c) =
      if ∀ v ∈ d.support, v.1 ∉ T then monomial d c else 0 := by
  rw [killBlocks, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    exact Finsupp.prod_congr fun v hv => by rw [if_neg (h v hv)]
  · simp only [not_forall, not_not] at h
    obtain ⟨v, hv, hT⟩ := h
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)
    dsimp only
    rw [if_pos hT, zero_pow (Finsupp.mem_support_iff.mp hv)]
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
