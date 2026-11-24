-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.MulStable.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:29.179599+00:00
-- url     : https://prove2.me/submissions/4deb0a5b-85c7-42c4-8ab4-20dce92b2c32

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]
namespace ReciprocityTheory.PGsh.Up
namespace MulStable
theorem _root_.solution {S : Submodule k ((ι → ZMod p) → k)} {s : Finset ι}
    {h : ι → (ι → ZMod p) → k} (a : ∀ i ∈ s, MulStable S (h i)) :
    MulStable S (∑ i ∈ s, h i) := by
  revert a
  refine Finset.induction_on s ?_ ?_
  · intro _ f _
    simp
  · intro j s hj ih a
    rw [Finset.sum_insert hj]
    exact (a j (Finset.mem_insert_self j s)).add (ih fun i hi => a i (Finset.mem_insert_of_mem hi))
end MulStable
end ReciprocityTheory.PGsh.Up
