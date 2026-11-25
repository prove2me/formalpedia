-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_hilbFn_map_c5a78f77fece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:41.01306+00:00
-- url     : https://prove2.me/submissions/7647bdb1-ad3f-4011-9de0-cf7eeb9acad5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_finrank_gradedPiece_28c37d509f1a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution (V : Ideal (MRing ι F)) (m' : K ⊕ Unit → ℤ) :
    hilbFn (V.map (rename (liftVar (ι := ι) ptIdx))) m' =
      if 0 ≤ m' (.inr ()) then hilbFn V (fun k => m' (.inl k)) else 0 := by
  unfold hilbFn
  by_cases ht : 0 ≤ m' (.inr ())
  · rw [if_pos ht]
    by_cases hk : ∀ k, 0 ≤ m' (.inl k)
    · have hall : ∀ x, 0 ≤ m' x := by
        rintro (k | u)
        · exact hk k
        · cases u
          exact ht
      rw [if_pos hall, if_pos hk, finrank_gradedPiece]
      rfl
    · have hall : ¬ ∀ x, 0 ≤ m' x := fun h => hk fun k => h _
      rw [if_neg hall, if_neg hk]
  · rw [if_neg ht, if_neg (fun h => ht (h _))]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
