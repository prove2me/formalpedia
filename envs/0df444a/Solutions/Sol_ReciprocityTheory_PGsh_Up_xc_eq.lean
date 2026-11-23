-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.xc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:17.326622+00:00
-- url     : https://prove2.me/submissions/55923497-e318-4c04-aa1c-2c829bb3b5f6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate

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
theorem _root_.solution (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) (i : ι) (x : ι → ZMod p) :
    xc k i x = ∑ m, Cinv i m * lam Cm m x := by
  have e : ∀ i', ∑ m, Cinv i m * Cm m i' = (1 : Matrix ι ι k) i i' := by
    intro i'; rw [← h, Matrix.mul_apply]
  simp only [lam, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, e, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
end ReciprocityTheory.PGsh.Up
