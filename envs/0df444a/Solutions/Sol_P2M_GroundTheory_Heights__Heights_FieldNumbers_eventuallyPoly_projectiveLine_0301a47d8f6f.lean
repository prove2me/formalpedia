-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_eventuallyPoly_projectiveLine_0301a47d8f6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:23.9847+00:00
-- url     : https://prove2.me/submissions/3210b02c-bb1f-4f0a-94b1-34609a0fe56a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_hilbFn_projectiveSpace_2488abe8fe91

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
theorem _root_.solution :
    EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) :=
  (Filter.eventually_ge_atTop 0).mono fun m hm => by
    have ht : (0 : ℤ) ≤ m () := hm ()
    rw [hilbFn_projectiveSpace, binomFn, if_pos ht, Nat.choose_one_right]
    have e : (((m ()).toNat : ℕ) : ℤ) = m () := Int.toNat_of_nonneg ht
    have e' : (((m ()).toNat : ℕ) : ℚ) = (m () : ℚ) := by exact_mod_cast e
    simp only [map_add, eval_X, map_one]
    push_cast
    rw [e']
end GroundTheory.Heights₂.Heights.FieldNumbers
