-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.val_prim_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:14.341902+00:00
-- url     : https://prove2.me/submissions/5f035fa9-e706-4b5f-b3c1-121caca9cc56

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_val_sub_one_le

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution {z : C} (hz : IsPrimitiveRoot z p) : v (z - 1) ^ (p - 1) = v (p : C) := by
  have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have h1 : (p : C) = ∏ μ ∈ primitiveRoots p C, (1 - μ) := by
    have := congrArg (Polynomial.eval 1) hcyc
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at this
    simpa using this
  have hc : ∀ μ ∈ primitiveRoots p C, v (1 - μ) = v (z - 1) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.out.pos).mp hμ
    rw [Valuation.map_sub_swap]
    exact le_antisymm (val_sub_one_le hμ' hz) (val_sub_one_le hz hμ')
  rw [h1, map_prod, Finset.prod_congr rfl hc, Finset.prod_const, hz.card_primitiveRoots,
    Nat.totient_prime hp.out]
end ReciprocityTheory.PGsh.Up.U3
