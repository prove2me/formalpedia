-- Prove2me | solution 1 for QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9ae0d98f-683b-5805-a7f5-bdeff7df7e68

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
import Theorems.Thm_Rat_forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg
import Theorems.Thm_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem
import Theorems.Thm_Rat_exists_sq_eq_adicCompletion_of_eight_dvd_sub_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace E2cChi

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

theorem iso_at_two (q : ℕ) (h5 : q % 8 = 5) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (2 : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ z x y : w.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-2)) * x ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-(q : ℚ))) * y ^ 2 = 0 := by
  haveI : CharZero (w.adicCompletion ℚ) := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  obtain ⟨s, hs⟩ := Rat.exists_sq_eq_adicCompletion_of_eight_dvd_sub_one w hw (-q - 2) (by omega)
  refine ⟨s, 1, 1, fun hh => one_ne_zero hh.2.2, ?_⟩
  have hs' : s ^ 2 = -(q : w.adicCompletion ℚ) - 2 := by
    rw [hs]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_ofNat, map_sub, map_neg, map_natCast, map_ofNat]
  simp only [map_neg, map_ofNat, map_natCast]
  linear_combination hs'

theorem main (q : ℕ) (hq : q.Prime) (h5 : q % 8 = 5) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-2 : ℚ) (-(q : ℚ)) q := by
  haveI hcz : ∀ w : HeightOneSpectrum (𝓞 ℚ), CharZero (w.adicCompletion ℚ) := fun w =>
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq.pos
  refine ⟨by norm_num, by linarith, fun v => ?_⟩

  have hunit : ∀ w : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ w.asIdeal → (((-2 : ℤ)) : 𝓞 ℚ) ∉ w.asIdeal := by
    intro w h2 h
    apply h2
    have := w.asIdeal.neg_mem_iff.mpr h
    push_cast at this
    simpa using this
  have hiso : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      ∃ z x y : w.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-2)) * x ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-(q : ℚ))) * y ^ 2 = 0 := by
    intro w hw
    by_cases h2 : (2 : 𝓞 ℚ) ∈ w.asIdeal
    · exact iso_at_two q h5 w h2
    · have hnq : (((-(q : ℤ)) : ℤ) : 𝓞 ℚ) ∉ w.asIdeal := by
        intro h
        apply hw
        have := w.asIdeal.neg_mem_iff.mp (by push_cast at h ⊢; exact h)
        exact_mod_cast this
      have h := Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem (-2) (-(q : ℤ)) w h2 (hunit w h2) hnq
      simp only [Int.cast_neg, Int.cast_natCast, Int.cast_ofNat, map_neg, map_natCast, map_ofNat] at h ⊢
      exact h
  have hpar := Rat.forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg (-2) (-(q : ℚ)) (by norm_num) (by linarith)
    q hq hiso v
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero,
    QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero _ _ _ (by norm_num)
      (by haveI := hcz v; rw [Rat.cast_neg, neg_ne_zero, Rat.cast_natCast]; exact_mod_cast hq.ne_zero),
    aniso_iff, hpar]

end E2cChi

theorem solution (q : ℕ) (hq : q.Prime) (h5 : q % 8 = 5) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-2 : ℚ) (-(q : ℚ)) q :=
  E2cChi.main q hq h5

end S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five
end P2MW
export P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five (solution)
