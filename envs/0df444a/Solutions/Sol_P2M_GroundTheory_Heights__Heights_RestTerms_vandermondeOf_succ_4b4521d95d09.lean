-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_succ_4b4521d95d09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:14:12.637913+00:00
-- url     : https://prove2.me/submissions/d632cac9-779f-4eb6-9855-92ced19cb407

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookTableauCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) :
    vandermondeOf v =
      (∏ j : Fin n, (v 0 - v j.succ)) * vandermondeOf (fun j : Fin n => v j.succ) := by
  have key : ∀ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v i - v j) =
      ∏ j : Fin (n + 1), if i < j then v i - v j else 1 := by
    intro i
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  unfold vandermondeOf
  simp only [key]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.succ_lt_succ_iff, Fin.not_lt_zero, if_false, one_mul]
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
end GroundTheory.Heights₂.Heights.RestTerms
