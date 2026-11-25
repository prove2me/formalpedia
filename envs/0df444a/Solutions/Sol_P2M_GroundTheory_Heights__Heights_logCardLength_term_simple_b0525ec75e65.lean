-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logCardLength_term_simple_b0525ec75e65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:40.956888+00:00
-- url     : https://prove2.me/submissions/f4ae6ea2-704e-493f-a9ab-be7b3b42c04b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_term_eq_8e0283e60fb9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_term_of_not_5772e4436efb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_simple_26bd67a2a4aa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}
namespace GroundTheory.Heights₂.Heights.logCardLength
theorem _root_.solution (M : Type) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (I : Ideal R) (hI : I.IsMaximal) (hkill : ∀ a ∈ I, ∀ x : M, a • x = 0)
    (hcard : Nat.card M = Nat.card (R ⧸ I)) (m : Ideal R) :
    term R M m = if m = I then Real.log (Nat.card M) else 0 := by
  by_cases hm : m.IsMaximal
  · rw [term_eq, length_loc_simple M I hI hkill m]
    split_ifs with h
    · subst h; simp [hcard]
    · simp
  · rw [term_of_not M m hm, if_neg (fun (h : m = I) => hm (h ▸ hI))]
end GroundTheory.Heights₂.Heights.logCardLength
