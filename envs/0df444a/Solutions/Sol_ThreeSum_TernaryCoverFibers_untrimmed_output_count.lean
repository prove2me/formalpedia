-- Prove2me | solution 1 for ThreeSum.TernaryCoverFibers.untrimmed_output_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:18.287492+00:00
-- url     : https://prove2.me/submissions/595a9bef-2383-4469-8dd5-0205214cc21e

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverFibers
open Finset
open scoped BigOperators
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
variable [DecidableEq Q] [DecidableEq K] [AddCommGroup K]
namespace ThreeSum.TernaryCoverFibers
theorem _root_.solution (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G)
    (hadd : ∀ e : E, left e + right e = outputHash (output e)) (o : K) :
    (univ.filter fun e => left e + right e = o).card =
      G * outputFiberCount outputHash o := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := univ.filter fun e => left e + right e = o)
    (t := univ.filter fun q => outputHash q = o) (f := output)
    (by
      intro e he
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [← hadd e]
      exact (mem_filter.mp he).2)
  rw [hpartition]
  have hterm : ∀ q ∈ (univ.filter fun q => outputHash q = o),
      ((univ.filter fun e => left e + right e = o).filter
        fun e => output e = q).card = G := by
    intro q hq
    have heq : ((univ.filter fun e => left e + right e = o).filter
        fun e => output e = q) = (univ.filter fun e => output e = q) := by
      ext e
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro he
        refine ⟨?_, he⟩
        rw [hadd e, he]
        exact (mem_filter.mp hq).2
    rw [heq]
    exact hfiber q
  calc
    _ = ∑ _q ∈ (univ.filter fun q => outputHash q = o), G := sum_congr rfl hterm
    _ = G * outputFiberCount outputHash o := by
      simp [outputFiberCount, Nat.mul_comm]
end ThreeSum.TernaryCoverFibers
