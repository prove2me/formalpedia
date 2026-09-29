-- Prove2me | solution 1 for RubinSilverberg.isIcoSymmetry_icoS
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/623e6b7d-9092-53bc-8a17-526617e01523

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_isIcoSymmetry_icoS

open RubinSilverberg

theorem solution {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) : IsIcoSymmetry (icoS ζ) := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have h : ∀ k : ℕ, ζ ^ (5 * k) = 1 := fun k => by rw [pow_mul, h5, one_pow]
  have hζ0 : ζ ≠ 0 := by
    intro h0; rw [h0] at h5; norm_num at h5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [icoS, Matrix.det_fin_two_of]
    linear_combination h5
  · intro n d
    simp only [icoS, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, kleinVHom]
    ring_nf
    simp only [show ζ ^ 35 = 1 from h 7, show ζ ^ 30 = 1 from h 6, show ζ ^ 25 = 1 from h 5]
    ring
  · intro n d
    simp only [icoS, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, kleinHHom]
    ring_nf
    simp only [show ζ ^ 60 = 1 from h 12, show ζ ^ 55 = 1 from h 11, show ζ ^ 50 = 1 from h 10,
      show ζ ^ 45 = 1 from h 9, show ζ ^ 40 = 1 from h 8]
    ring
  · intro n d
    simp only [icoS, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, kleinTHom]
    ring_nf
    simp only [show ζ ^ 90 = 1 from h 18, show ζ ^ 85 = 1 from h 17, show ζ ^ 80 = 1 from h 16,
      show ζ ^ 70 = 1 from h 14, show ζ ^ 65 = 1 from h 13, show ζ ^ 60 = 1 from h 12]
    ring
  · intro u hV hden
    have hu : u ≠ 0 := by
      rintro rfl; apply hV; simp [kleinV]
    have hf : u ^ 10 + 11 * u ^ 5 - 1 ≠ 0 := by
      intro h'; apply hV; simp [kleinV, h']
    have hm : moeb (icoS ζ) u = ζ * u := by
      simp [moeb, icoS]
      field_simp
    have hd : moebDen (icoS ζ) u = ζ ^ 2 := by
      simp [moebDen, icoS]
    have hT : kleinT (ζ * u) = kleinT u := by
      unfold kleinT; ring_nf
      simp only [show ζ ^ 30 = 1 from h 6, show ζ ^ 25 = 1 from h 5, show ζ ^ 20 = 1 from h 4,
        show ζ ^ 10 = 1 from h 2, h5]
      ring
    have hfz : (ζ * u) ^ 10 + 11 * (ζ * u) ^ 5 - 1 = u ^ 10 + 11 * u ^ 5 - 1 := by
      ring_nf; simp only [show ζ ^ 10 = 1 from h 2, h5]; ring
    have hG : 57 * (ζ * u) ^ 15 - 247 * (ζ * u) ^ 10 - 171 * (ζ * u) ^ 5 - 1
        = 57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1 := by
      ring_nf; simp only [show ζ ^ 15 = 1 from h 3, show ζ ^ 10 = 1 from h 2, h5]; ring
    have hΓ : (ζ * u) ^ 15 - 171 * (ζ * u) ^ 10 + 247 * (ζ * u) ^ 5 + 57
        = u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57 := by
      ring_nf; simp only [show ζ ^ 15 = 1 from h 3, show ζ ^ 10 = 1 from h 2, h5]; ring
    rw [hm, hd]
    simp only [icoS, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    unfold rsBeta rsGamma
    rw [hT, hfz, hG, hΓ]
    have hD1 : (144 : K) * (ζ ^ 4 * u ^ 4) * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ hζ0) (pow_ne_zero _ hu)))
        (pow_ne_zero _ hf)
    have hD2 : (144 : K) * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hu)) (pow_ne_zero _ hf)
    constructor
    · rw [mul_pow, zero_mul, add_zero, ← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff hD1 hD2]
      linear_combination
        (-(ζ ^ 2 * (kleinT u * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1))
          * (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4))) * h5
    · ring

end S_RubinSilverberg_isIcoSymmetry_icoS
end P2MW
export P2MW.S_RubinSilverberg_isIcoSymmetry_icoS (solution)
