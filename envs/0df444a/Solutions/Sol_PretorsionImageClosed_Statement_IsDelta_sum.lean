-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsDelta.sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:47.246361+00:00
-- url     : https://prove2.me/submissions/bb618b01-52ee-4a42-aa17-e3c036c9f434

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Theorems.Thm_PretorsionImageClosed_Statement_isDelta_zero

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial
namespace PretorsionImageClosed.Statement
namespace IsDelta
theorem _root_.solution {ι : Type*} (s : Finset ι) (f g : ι → Rq[X])
    (h : ∀ i ∈ s, IsDelta (f i) (g i)) : IsDelta (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isDelta_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end IsDelta
end PretorsionImageClosed.Statement
