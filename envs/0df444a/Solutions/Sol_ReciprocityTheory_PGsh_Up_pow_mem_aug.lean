-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.pow_mem_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:41:15.599894+00:00
-- url     : https://prove2.me/submissions/ec6d6ac4-a413-4c50-b931-f99c9fe4aa9d

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    [AddCommGroup X] [Fintype X] [DecidableEq X] (A : HopfOrder (C := C) R X) {x : X → C}
    (hx : x ∈ augIdeal A.carrier) : ∀ k : ℕ, x ^ (k + 1) ∈ augIdeal A.carrier := by
  intro k
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply] at hx ⊢
  refine ⟨?_, by rw [Pi.pow_apply, hx.2, zero_pow (Nat.succ_ne_zero k)]⟩
  induction k with
  | zero => rw [zero_add, pow_one]; exact hx.1
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hx.1
end ReciprocityTheory.PGsh.Up
