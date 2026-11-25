-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.val_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:26.807897+00:00
-- url     : https://prove2.me/submissions/d03b793a-7fc8-479a-8b5d-0ee711085071

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_pow_sub_le

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
theorem _root_.solution {α β : C} (hα : IsPrimitiveRoot α p) (hβ : IsPrimitiveRoot β p) :
    v (α - 1) ≤ v (β - 1) := by
  obtain ⟨i, -, hi⟩ := hβ.eq_pow_of_pow_eq_one hα.pow_eq_one
  have hβ1 : v β = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le' hp.out.ne_zero).mp (by rw [← map_pow, hβ.pow_eq_one, map_one])
  rw [← hi]
  have := v_pow_sub_le (v := v) (r := β) (s := 1) hβ1.le (by rw [map_one]) i
  rwa [one_pow] at this
end ReciprocityTheory.PGsh.Up.U3
