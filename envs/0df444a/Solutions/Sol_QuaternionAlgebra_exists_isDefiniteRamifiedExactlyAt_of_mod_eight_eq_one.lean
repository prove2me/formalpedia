-- Prove2me | solution 1 for QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/23548dae-df0e-5d60-8b73-7bb2626c66a6

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
import Theorems.Thm_Rat_forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg
import Theorems.Thm_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem
import Theorems.Thm_Rat_exists_sq_eq_adicCompletion_of_eight_dvd_sub_one
import Theorems.Thm_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace E2dChi

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

theorem exists_prime_aux (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    ∃ r : ℕ, r.Prime ∧ q < r ∧ r % 8 = 3 ∧ ¬ IsSquare ((r : ℤ) : ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hchar : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hchar
  have hc0 : c ≠ 0 := fun h => hc (h ▸ IsSquare.zero)
  have hcop : Nat.Coprime 8 q := by
    have h2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
    simpa using h2q.pow_left 3
  let e := ZMod.chineseRemainder hcop
  let a₀ : ZMod (8 * q) := e.symm (3, c)
  have ha₀ : IsUnit a₀ := by
    have h3 : IsUnit (3 : ZMod 8) := by decide
    have : IsUnit ((3 : ZMod 8), c) := Prod.isUnit_iff.mpr ⟨h3, isUnit_iff_ne_zero.mpr hc0⟩
    exact this.map e.symm
  haveI : NeZero (8 * q) := ⟨Nat.mul_ne_zero (by norm_num) hq.ne_zero⟩
  obtain ⟨r, hqr, hr, hra⟩ := Nat.forall_exists_prime_gt_and_eq_mod ha₀ q
  have her : e (r : ZMod (8 * q)) = ((3 : ZMod 8), c) := by
    rw [hra]; exact e.apply_symm_apply _
  rw [map_natCast] at her
  have h8 : (r : ZMod 8) = 3 := by simpa using congrArg Prod.fst her
  have hqc : (r : ZMod q) = c := by simpa using congrArg Prod.snd her
  refine ⟨r, hr, hqr, ?_, ?_⟩
  · have := (ZMod.natCast_eq_natCast_iff' r 3 8).mp (by simpa using h8)
    simpa using this
  · rw [Int.cast_natCast, hqc]; exact hc

theorem iso_at_two (r q : ℕ) (hr : r % 8 = 3) (hq : q % 8 = 1) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (2 : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ z x y : w.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-(r : ℚ))) * x ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-(q : ℚ))) * y ^ 2 = 0 := by
  haveI : CharZero (w.adicCompletion ℚ) := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  obtain ⟨s, hs⟩ := Rat.exists_sq_eq_adicCompletion_of_eight_dvd_sub_one w hw (-r - 4 * q) (by omega)
  refine ⟨s, 1, 2, fun hh => one_ne_zero hh.2.1, ?_⟩
  have hs' : s ^ 2 = -(r : w.adicCompletion ℚ) - 4 * q := by
    rw [hs]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, map_sub, map_neg, map_mul,
      map_natCast, map_ofNat]
  simp only [map_neg, map_natCast]
  linear_combination hs'

theorem iso_at_r (r q : ℕ) (hr : r.Prime) (hq : q.Prime) (hrq : q < r) (hr8 : r % 8 = 3) (hq8 : q % 8 = 1)
    (hnr : ¬ IsSquare ((r : ℤ) : ZMod q)) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (r : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ z x y : w.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-(r : ℚ))) * x ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-(q : ℚ))) * y ^ 2 = 0 := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hr2 : r ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hndvd : ¬ (r : ℤ) ∣ -(q : ℤ) := by
    rw [dvd_neg]
    intro h
    have h' : r ∣ q := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hr hq).mp h'
    omega

  have hleg : legendreSym r (-(q : ℤ)) = 1 := by
    rw [show (-(q : ℤ)) = (-1) * q by ring, legendreSym.mul, legendreSym.at_neg_one hr2,
      ZMod.χ₄_nat_three_mod_four (by omega : r % 4 = 3),
      legendreSym.quadratic_reciprocity_one_mod_four (by omega : q % 4 = 1) hr2,
      (legendreSym.eq_neg_one_iff q).mpr hnr]
    norm_num
  have h0 : ((-(q : ℤ) : ℤ) : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hndvd
  have hsq : IsSquare ((-(q : ℤ) : ℤ) : ZMod r) := (legendreSym.eq_one_iff r h0).mp hleg
  obtain ⟨s, hs⟩ := Rat.exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd r hr hr2 w hw (-(q : ℤ)) hndvd hsq
  refine ⟨s, 0, 1, fun hh => one_ne_zero hh.2.2, ?_⟩
  have hs' : s ^ 2 = -(q : w.adicCompletion ℚ) := by
    rw [hs]
    simp only [Int.cast_neg, Int.cast_natCast, map_neg, map_natCast]
  simp only [map_neg, map_natCast]
  linear_combination hs'

theorem main (q : ℕ) (hq : q.Prime) (h1 : q % 8 = 1) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q := by
  haveI hcz : ∀ w : HeightOneSpectrum (𝓞 ℚ), CharZero (w.adicCompletion ℚ) := fun w =>
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hq2 : q ≠ 2 := by omega
  obtain ⟨r, hr, hqr, hr8, hnr⟩ := exists_prime_aux q hq hq2
  have hrpos : (0 : ℚ) < r := by exact_mod_cast hr.pos
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq.pos
  refine ⟨-(r : ℚ), -(q : ℚ), by linarith, by linarith, fun v => ?_⟩
  have hiso : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      ∃ z x y : w.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-(r : ℚ))) * x ^ 2 - (algebraMap ℚ (w.adicCompletion ℚ) (-(q : ℚ))) * y ^ 2 = 0 := by
    intro w hw
    by_cases h2 : (2 : 𝓞 ℚ) ∈ w.asIdeal
    · exact iso_at_two r q hr8 h1 w h2
    · by_cases hrw : ((r : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
      · exact iso_at_r r q hr hq hqr hr8 h1 hnr w hrw
      · have hnr' : (((-(r : ℤ)) : ℤ) : 𝓞 ℚ) ∉ w.asIdeal := by
          intro h
          apply hrw
          have := w.asIdeal.neg_mem_iff.mp (by push_cast at h ⊢; exact h)
          exact_mod_cast this
        have hnq : (((-(q : ℤ)) : ℤ) : 𝓞 ℚ) ∉ w.asIdeal := by
          intro h
          apply hw
          have := w.asIdeal.neg_mem_iff.mp (by push_cast at h ⊢; exact h)
          exact_mod_cast this
        have h := Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem (-(r : ℤ)) (-(q : ℤ)) w h2 hnr' hnq
        simp only [Int.cast_neg, Int.cast_natCast, map_neg, map_natCast] at h ⊢
        exact h
  have hpar := Rat.forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg (-(r : ℚ)) (-(q : ℚ))
    (by linarith) (by linarith) q hq hiso v
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero,
    QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero _ _ _
      (by haveI := hcz v; rw [Rat.cast_neg, neg_ne_zero, Rat.cast_natCast]; exact_mod_cast hr.ne_zero)
      (by haveI := hcz v; rw [Rat.cast_neg, neg_ne_zero, Rat.cast_natCast]; exact_mod_cast hq.ne_zero),
    aniso_iff, hpar]

end E2dChi

theorem solution (q : ℕ) (hq : q.Prime) (h1 : q % 8 = 1) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q :=
  E2dChi.main q hq h1

end S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one
end P2MW
export P2MW.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one (solution)
