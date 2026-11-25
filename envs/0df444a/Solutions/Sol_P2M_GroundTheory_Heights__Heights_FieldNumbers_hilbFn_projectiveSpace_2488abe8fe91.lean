-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_hilbFn_projectiveSpace_2488abe8fe91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:39.03901+00:00
-- url     : https://prove2.me/submissions/c3d4559a-e4d6-4d0d-85ca-2bf2955c91a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_projectiveSpace_951d850aa297

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
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (F : Type*) [Field F] (N : ℕ) (m : Unit → ℤ) :
    hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) m = binomFn N (m ()) := by
  unfold hilbFn binomFn
  by_cases hm : 0 ≤ m ()
  · rw [if_pos (fun k => hm), if_pos hm]
    have : (fun k => (m k).toNat) = fun _ : Unit => (m ()).toNat := rfl
    rw [this, finrank_gradedPiece_projectiveSpace]
  · rw [if_neg (fun h => hm (h ())), if_neg hm]
end GroundTheory.Heights₂.Heights.FieldNumbers
