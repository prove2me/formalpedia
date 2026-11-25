-- Prove2me | solution 1 for SNumbers.signedSum_insert_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:09:51.025086+00:00
-- url     : https://prove2.me/submissions/84a62b36-42e9-4f9f-9ce6-3e61be29efd1

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_signedSum_empty
attribute [local simp] SNumbers.signedSum_empty

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {G : Type*} [AddCommGroup G] {ι : Type*} [DecidableEq ι]
namespace SNumbers
theorem _root_.solution {w : ι → G} {a : ι} {S J : Finset ι} (ha : a ∉ J) :
    signedSum w (insert a S) (insert a J) = signedSum w S J + w a := by
  rw [signedSum, signedSum, Finset.sum_insert ha, if_pos (Finset.mem_insert_self a S)]
  have hcongr : ∀ j ∈ J, (if j ∈ insert a S then w j else -w j)
      = if j ∈ S then w j else -w j := by
    intro j hj
    have hja : j ≠ a := fun h => ha (h ▸ hj)
    simp [Finset.mem_insert, hja]
  rw [Finset.sum_congr rfl hcongr]
  abel
end SNumbers
