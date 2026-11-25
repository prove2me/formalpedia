-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_eq_mixedDiff_6117ca062b3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:23.271486+00:00
-- url     : https://prove2.me/submissions/5ea2c1c3-067a-4a86-a9eb-f07a82e7c272

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_cons_912e7bd7a1f6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
variable {K : Type} [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
theorem _root_.solution (f : (K → ℤ) → ℤ) (c : ℕ) (L : List K) (t : K → ℕ) :
    listDiff L (fun t => (f (fun k => (c : ℤ) + t k) : ℚ)) t =
      (((L.map fun k => (Pi.single k 1 : K → ℤ)).foldr diffStep f)
        (fun k => (c : ℤ) + t k + L.count k) : ℚ) := by
  induction L generalizing t with
  | nil => simp [listDiff]
  | cons k L ih =>
    rw [listDiff_cons, ih, ih, List.map_cons, List.foldr_cons, diffStep, Int.cast_sub]
    have a1 : (fun i => (c : ℤ) + (((t + Pi.single k 1 : K → ℕ) i : ℕ) : ℤ) + (L.count i : ℤ)) =
        fun i => (c : ℤ) + t i + ((k :: L).count i : ℤ) := by
      funext i
      by_cases h : i = k
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    have a2 : (fun i => (c : ℤ) + t i + (L.count i : ℤ)) =
        (fun i => (c : ℤ) + t i + ((k :: L).count i : ℤ)) - Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    rw [a1, a2]
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
