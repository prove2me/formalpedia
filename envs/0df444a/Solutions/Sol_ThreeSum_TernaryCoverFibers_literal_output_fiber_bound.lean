-- Prove2me | solution 1 for ThreeSum.TernaryCoverFibers.literal_output_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:52.271113+00:00
-- url     : https://prove2.me/submissions/3fbb11a2-6a79-4a9e-b6f8-15dc3d14cda2

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Theorems.Thm_ThreeSum_TernaryCoverFibers_sum_rawPairCount
import Theorems.Thm_ThreeSum_TernaryCoverFibers_untrimmed_output_count

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverFibers
open Finset
open scoped BigOperators
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
variable [DecidableEq Q] [DecidableEq K] [AddCommGroup K]
namespace ThreeSum.TernaryCoverFibers
theorem _root_.solution (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G τ : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G)
    (hadd : ∀ e : E, left e + right e = outputHash (output e))
    (hraw : ∀ a b : K, rawPairCount left right a b ≤ τ) (o : K) :
    G * outputFiberCount outputHash o ≤ Fintype.card K * τ := by
  rw [← untrimmed_output_count output outputHash left right G hfiber hadd o,
    ← sum_rawPairCount left right o]
  calc
    _ ≤ ∑ _a : K, τ := sum_le_sum (fun a _ => hraw a (o - a))
    _ = Fintype.card K * τ := by simp
end ThreeSum.TernaryCoverFibers
