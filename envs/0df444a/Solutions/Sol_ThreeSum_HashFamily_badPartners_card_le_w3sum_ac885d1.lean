-- Prove2me | solution 1 for ThreeSum.HashFamily.badPartners_card_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:39.243429+00:00
-- url     : https://prove2.me/submissions/04fece10-675c-44a6-a857-6d170fd093a8

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
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (left right : E → α → Bool) (e : E) (Delta G : ℕ)
    (hL : (Finset.univ.filter (fun f => left e = left f)).card ≤ Delta)
    (hR : (Finset.univ.filter (fun f => right e = right f)).card ≤ Delta)
    (hG : (Finset.univ.filter (fun f =>
      outputMask left right e = outputMask left right f)).card ≤ G) :
    (badPartners left right e).card ≤ 2 * Delta + G := by
  have he : badPartners left right e =
      ((Finset.univ.filter (fun f => left e = left f)) ∪
        (Finset.univ.filter (fun f => right e = right f))) ∪
          (Finset.univ.filter (fun f => outputMask left right e = outputMask left right f)) := by
    ext f
    simp [badPartners, or_assoc]
  rw [he]
  have hu := Finset.card_union_le
    ((Finset.univ.filter (fun f => left e = left f)) ∪
      (Finset.univ.filter (fun f => right e = right f)))
    (Finset.univ.filter (fun f => outputMask left right e = outputMask left right f))
  have hv := Finset.card_union_le (Finset.univ.filter (fun f => left e = left f))
    (Finset.univ.filter (fun f => right e = right f))
  omega
end ThreeSum.HashFamily
