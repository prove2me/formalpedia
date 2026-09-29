-- Prove2me | solution 1 for QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_one_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0b74b23d-3d9e-551f-9dba-f304e8c0f30e

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
import Theorems.Thm_Rat_forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg
import Theorems.Thm_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace E2aChi

theorem aniso_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℚ) :
    (∀ z x y : v.adicCompletion ℚ, z ^ 2 - (a : v.adicCompletion ℚ) * x ^ 2 - (b : v.adicCompletion ℚ) * y ^ 2 = 0 →
        z = 0 ∧ x = 0 ∧ y = 0) ↔
      ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
          z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0 := by
  rw [eq_ratCast, eq_ratCast]
  constructor
  · rintro h ⟨z, x, y, hne, h0⟩
    exact hne (h z x y h0)
  · intro h z x y h0
    by_contra hne
    exact h ⟨z, x, y, hne, h0⟩

theorem main : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-1 : ℚ) (-1) 2 := by
  refine ⟨by norm_num, by norm_num, fun v => ?_⟩

  have hunit : ∀ w : HeightOneSpectrum (𝓞 ℚ), (((-1 : ℤ)) : 𝓞 ℚ) ∉ w.asIdeal := by
    intro w h
    have : (1 : 𝓞 ℚ) ∈ w.asIdeal := by
      have := w.asIdeal.neg_mem_iff.mpr h
      push_cast at this
      simpa using this
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hiso : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((2 : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      ∃ z x y : w.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-1)) * x ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-1)) * y ^ 2 = 0 := by
    intro w hw
    have h := Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem (-1) (-1) w (by simpa using hw) (hunit w) (hunit w)
    simpa using h
  have hpar := Rat.forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg (-1) (-1) (by norm_num) (by norm_num)
    2 Nat.prime_two hiso v

  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero,
    QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero _ _ _ (by norm_num) (by norm_num),
    aniso_iff, hpar]

end E2aChi

theorem solution : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-1 : ℚ) (-1) 2 :=
  E2aChi.main

end S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two
end P2MW
export P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two (solution)
