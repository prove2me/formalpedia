-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.pow_pred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:18.128886+00:00
-- url     : https://prove2.me/submissions/4432b43f-452b-49b6-9082-3628275626b8

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
open ReciprocityTheory.PGsh.Up.U3.IsTeich
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
namespace ReciprocityTheory.PGsh.Up.U3.IsTeich
theorem _root_.solution {a : ZMod p} (ha : a ≠ 0) : ω a ^ (p - 1) = 1 := by
  have hne := hω.ne_zero ha
  have h1 : ω a ^ (p - 1) * ω a = 1 * ω a := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, one_mul]
    exact hω.pow a
  exact mul_right_cancel₀ hne h1
end ReciprocityTheory.PGsh.Up.U3.IsTeich
