-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.MulStable.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:05.315687+00:00
-- url     : https://prove2.me/submissions/d12d5e77-fee3-45ad-831c-d0548e38ea86

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul

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
    MulStable S (∏ i ∈ s, h i) := by
  revert a
  refine Finset.induction_on s ?_ ?_
  · intro _ f hf
    simpa using hf
  · intro j s hj ih a
    rw [Finset.prod_insert hj]
    exact (a j (Finset.mem_insert_self j s)).mul (ih fun i hi => a i (Finset.mem_insert_of_mem hi))
end MulStable
end ReciprocityTheory.PGsh.Up
