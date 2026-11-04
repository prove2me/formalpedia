-- Prove2me | solution 1 for ThreeSum.HashFamily.raw_second_moment_five_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:42.614713+00:00
-- url     : https://prove2.me/submissions/59456fa6-dc97-4722-9935-22d2feda27fe

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
import Definitions.Def_WeightedCache3SUM_Alias_738feef3d509e8a3
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ B)
    (hBp : B ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) :
    Fintype.card K ^ 2 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by
  have hp : 0 < Fintype.card K ^ 2 := pow_pos Fintype.card_pos _
  have hs := raw_second_moment left right hinj hcross B hB a b
  have hE : Fintype.card E ^ 2 ≤ Fintype.card E * Fintype.card K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left (Fintype.card E) hEp
  have hBB : Fintype.card E * B * Fintype.card K ≤
      3 * Fintype.card E * Fintype.card K ^ 2 := by
    have h := Nat.mul_le_mul_right (Fintype.card K)
      (Nat.mul_le_mul_left (Fintype.card E) hBp)
    convert h using 1 <;> ring
  have hs' : Fintype.card K ^ 4 *
      (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
        Fintype.card (α × Bool → K) * (5 * Fintype.card E * Fintype.card K ^ 2) := by
    refine hs.trans (Nat.mul_le_mul_left _ ?_)
    nlinarith only [hE, hBB]
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card K ^ 2) ?_ hp
  convert hs' using 1 <;> ring
end ThreeSum.HashFamily
