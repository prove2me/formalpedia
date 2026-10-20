-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.rankOneCornerAlignment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:33:21.835732+00:00
-- url     : https://prove2.me/submissions/99b2c288-9cee-459b-b09e-8855a2e9cb0e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- If the corner quadratic form vanishes on `x` (via `A x = 0`), then `Bᴴ x = 0`. -/
theorem g52c_block_kill {d n : ℕ} (A : Mat d) (B : Matrix (Fin d) (Fin n) ℂ)
    (C : Mat n) (hpos : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (x : Fin d → ℂ) (hx : A *ᵥ x = 0) : Bᴴ *ᵥ x = 0 := by
  set w := Bᴴ *ᵥ x with hw
  have hxB : star x ⬝ᵥ (B *ᵥ w) = star w ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec, hw, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  have hwB : star w ⬝ᵥ (Bᴴ *ᵥ x) = star w ⬝ᵥ w := by rw [← hw]
  have key : ∀ s : ℝ, 0 ≤ -2 * s * (star w ⬝ᵥ w).re + s ^ 2 * (star w ⬝ᵥ (C *ᵥ w)).re := by
    intro s
    have h := hpos.dotProduct_mulVec_nonneg (Sum.elim x (-(s : ℂ) • w))
    rw [Matrix.fromBlocks_mulVec, Function.star_sumElim, sumElim_dotProduct_sumElim] at h
    have e1 : (Sum.elim x (-(s : ℂ) • w) ∘ Sum.inl) = x := rfl
    have e2 : (Sum.elim x (-(s : ℂ) • w) ∘ Sum.inr) = -(s : ℂ) • w := rfl
    rw [e1, e2, hx] at h
    simp only [zero_add, Matrix.mulVec_smul, dotProduct_smul, dotProduct_add,
      star_smul, smul_dotProduct, hxB, hwB, smul_eq_mul] at h
    have h' := (Complex.nonneg_iff.mp h).1
    simp only [star_neg, Complex.star_def, Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, Complex.zero_re,
      neg_zero, zero_mul, sub_zero, Complex.mul_im, mul_zero, add_zero] at h'
    nlinarith [h']
  have hk0 : 0 ≤ star w ⬝ᵥ w := dotProduct_star_self_nonneg w
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hk0
  have hre0 : (star w ⬝ᵥ w).re = 0 := by
    by_contra hne
    have hpos' : 0 < (star w ⬝ᵥ w).re := lt_of_le_of_ne hre (Ne.symm hne)
    set k := (star w ⬝ᵥ w).re
    set c := (star w ⬝ᵥ (C *ᵥ w)).re
    have hc1 : 0 < |c| + 1 := by positivity
    have := key (k / (|c| + 1))
    have hs : 0 < k / (|c| + 1) := div_pos hpos' hc1
    have h2 : k / (|c| + 1) * |c| < k := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc1]; nlinarith [abs_nonneg c]
    have h3 : c ≤ |c| := le_abs_self c
    set t := k / (|c| + 1) with ht
    have h5 : t ^ 2 * c ≤ t * (t * |c|) := by
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg t)
      nlinarith [this]
    have h6 : t * (t * |c|) < t * k := mul_lt_mul_of_pos_left h2 hs
    nlinarith [this, h5, h6, mul_pos hs hpos']
  have : star w ⬝ᵥ w = 0 := Complex.ext hre0 (by rw [← him]; rfl)
  exact dotProduct_star_self_eq_zero.mp this

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution {d n : ℕ} (A : Mat d) (B : Matrix (Fin d) (Fin n) ℂ)
    (C : Mat n) (psi : EuclideanSpace ℂ (Fin d)) (hpsi : psi ≠ 0)
    (hA : A = pureDensity psi) (hpos : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    Set.range B.mulVec ⊆ {x | ∃ a : ℂ, x = a • (fun i => psi i)} := by
  rintro _ ⟨y, rfl⟩
  set p : Fin d → ℂ := fun i => psi i with hp
  have hAx : ∀ x : Fin d → ℂ, star p ⬝ᵥ x = 0 → A *ᵥ x = 0 := by
    intro x hx
    ext a
    have : (A *ᵥ x) a = psi a * (star p ⬝ᵥ x) := by
      rw [hA]
      simp only [Matrix.mulVec, dotProduct, pureDensity, Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [hp, Pi.star_apply, RCLike.star_def]
      ring
    rw [this, hx, mul_zero]; rfl
  have hN : star p ⬝ᵥ p ≠ 0 := by
    intro h
    apply hpsi
    have := dotProduct_star_self_eq_zero.mp h
    ext i
    exact congrFun this i
  set v := B *ᵥ y with hv
  set a := (star p ⬝ᵥ v) / (star p ⬝ᵥ p) with ha
  set x := v - a • p with hx
  have hpx : star p ⬝ᵥ x = 0 := by
    rw [hx, dotProduct_sub, dotProduct_smul, smul_eq_mul, ha]
    field_simp; ring
  have hBx := g52c_block_kill A B C hpos x (hAx x hpx)
  have hxv : star x ⬝ᵥ v = 0 := by
    rw [hv, Matrix.dotProduct_mulVec, ← Matrix.conjTranspose_conjTranspose B,
      ← Matrix.star_mulVec, hBx]; simp
  have hxp : star x ⬝ᵥ p = 0 := by
    rw [Matrix.star_dotProduct, hpx, star_zero]
  have hxx : star x ⬝ᵥ x = 0 := by
    conv_lhs => rw [hx]
    rw [dotProduct_sub, dotProduct_smul, hxv, hxp]; simp
  have := dotProduct_star_self_eq_zero.mp hxx
  refine ⟨a, ?_⟩
  rw [hx, sub_eq_zero] at this
  exact this
