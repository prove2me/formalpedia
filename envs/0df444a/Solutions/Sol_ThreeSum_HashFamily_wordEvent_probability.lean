-- Prove2me | solution 1 for ThreeSum.HashFamily.wordEvent_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:23.63369+00:00
-- url     : https://prove2.me/submissions/6fbc5078-c726-4a10-99f4-27832216edcf

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_wordEvent_card
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K)
    (hwords : LinearIndependent K (fun i => oneHot (K := K) (words i))) :
    eventProbability (wordEvent words target) = 1 / (Fintype.card K : ℝ) ^ r := by
  have hp : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have ho : (0 : ℝ) < Fintype.card (α × Bool → K) := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card K : ℝ) ^ r * (wordEvent words target).card =
      Fintype.card (α × Bool → K) := by exact_mod_cast wordEvent_card words target hwords
  unfold eventProbability
  apply (div_eq_div_iff (ne_of_gt ho) (ne_of_gt (pow_pos hp _))).mpr
  simpa only [one_mul, mul_comm] using hc
end ThreeSum.HashFamily
