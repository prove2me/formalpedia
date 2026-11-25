-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_set_add_8aefba410a42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:21.605699+00:00
-- url     : https://prove2.me/submissions/86dcec8e-2135-4ae9-a965-826149c8a484

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_add_54a958a23352

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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (h : (K → ℤ) → ℤ) (b b' : K → ℤ) :
    ∀ (L : List (K → ℤ)) (i : ℕ), i < L.length → ∀ m : K → ℤ,
      (L.set i (b + b')).foldr diffStep h m =
        (L.set i b).foldr diffStep h m + (L.set i b').foldr diffStep h (m - b)
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: L, 0, _, m => by
      simp only [List.set_cons_zero, List.foldr_cons]
      exact diffStep_add b b' _ m
  | a :: L, i + 1, hi, m => by
      simp only [List.set_cons_succ, List.foldr_cons, diffStep]
      have hi' : i < L.length := by simpa using hi
      rw [solution h b b' L i hi' m, solution h b b' L i hi' (m - a),
        sub_right_comm m a b]
      ring
end GroundTheory.Heights₂.Heights.FieldNumbers
