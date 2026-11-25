-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.lam_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:20.24103+00:00
-- url     : https://prove2.me/submissions/0876d424-315b-4483-9f2a-6e1c340d4813

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Theorems.Thm_ReciprocityTheory_PGsh_Up_xc_pow

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
theorem _root_.solution (Cm : Matrix ι ι k) (j : ι) (x : ι → ZMod p) :
    lam Cm j x ^ p = ∑ i, Cm j i ^ p * xc k i x := by
  simp only [lam, sum_pow_char, mul_pow, xc_pow]
end ReciprocityTheory.PGsh.Up
