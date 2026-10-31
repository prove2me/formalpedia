-- Prove2me | solution 1 for OddGoldbach19.cosecant_bound_of_cotangent_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:39:59.595327+00:00
-- url     : https://prove2.me/submissions/3abdc8e3-cfe4-4080-87ef-b54f1c2a1753

import Mathlib

set_option autoImplicit false
open scoped BigOperators ComplexConjugate

namespace OddGoldbach19

lemma cot_double_lift (z : ℂ) (hz : Complex.sin z ≠ 0) :
    2 * Complex.cot (z / 2) - Complex.cot (z / 2 - (Real.pi : ℂ) / 2) -
      Complex.cot (z / 2 + (Real.pi : ℂ) / 2) = 4 / Complex.sin z := by
  have he : 2 * (z / 2) = z := by ring
  have hs : Complex.sin (z / 2) ≠ 0 := by
    intro h; apply hz; rw [← he, Complex.sin_two_mul, h]; ring
  have hc : Complex.cos (z / 2) ≠ 0 := by
    intro h; apply hz; rw [← he, Complex.sin_two_mul, h]; ring
  simp only [Complex.cot_eq_cos_div_sin, Complex.cos_sub_pi_div_two,
    Complex.sin_sub_pi_div_two, Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two]
  rw [← he, Complex.sin_two_mul]
  field_simp
  linear_combination 4 * Complex.sin_sq_add_cos_sq (z / 2)

lemma sin_gap_ne_zero (x d : ℝ) (hd : 0 < d)
    (hgap : ∀ m : ℤ, d ≤ |x + m|) :
    Complex.sin ((Real.pi : ℂ) * (x : ℂ)) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k hk
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hx : (x : ℂ) = (k : ℂ) := by
    apply mul_left_cancel₀ hp
    calc (Real.pi : ℂ) * (x : ℂ) = (k : ℂ) * (Real.pi : ℂ) := hk
      _ = _ := mul_comm _ _
  have hx' : x = (k : ℝ) := by exact_mod_cast hx
  have h := hgap (-k)
  simp only [hx', Int.cast_neg, add_neg_cancel, abs_zero] at h
  exact (not_le_of_gt hd) h

end OddGoldbach19
open OddGoldbach19
/-- Antiperiodic doubling removes the factor-three loss in the cotangent-to-cosecant transfer. -/
theorem solution (C : ℝ)
    (hCot : ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (θ δ : κ → ℝ) (v : κ → ℂ),
      (∀ r, 0 < δ r) → (∀ r, δ r ≤ 1) →
      (∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) →
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) * ((Real.pi : ℂ) *
          Complex.cot ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))‖ ≤
        C * ∑ r, ‖v r‖ ^ 2 / δ r)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) * ((Real.pi : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))⁻¹)‖ ≤
      C * ∑ r, ‖v r‖ ^ 2 / δ r := by
  classical
  let t : ι × Fin 2 → ℝ := fun q => θ q.1 / 2 + q.2 / 2
  let d : ι × Fin 2 → ℝ := fun q => δ q.1 / 2
  let w : ι × Fin 2 → ℂ := fun q => if q.2 = 0 then v q.1 else -v q.1
  have hspacing : ∀ r s : ι × Fin 2, r ≠ s → ∀ m : ℤ, d r ≤ |t r - t s + m| := by
    rintro ⟨r, i⟩ ⟨s, j⟩ hne m
    by_cases hrs : r = s
    · subst s
      have hij : i ≠ j := by intro h; subst j; exact hne rfl
      have hm : m ≤ -1 ∨ 0 ≤ m := by omega
      fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
      all_goals
        dsimp [t, d]
        rcases hm with hm | hm
        · have hmR : (m : ℝ) ≤ -1 := by exact_mod_cast hm
          rw [abs_of_nonpos (by linarith)]
          linarith [hunit r]
        · have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
          by_cases hm0 : m = 0
          · subst m; norm_num; linarith [hunit r]
          · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
            rw [abs_of_nonneg (by linarith)]
            linarith [hunit r]
    · have h' := div_le_div_of_nonneg_right
        (hgap r s hrs ((i : ℤ) - (j : ℤ) + 2 * m)) (by norm_num : (0 : ℝ) ≤ 2)
      dsimp [t, d]
      calc δ r / 2 ≤ |θ r - θ s + ((i : ℤ) - (j : ℤ) + 2 * m : ℤ)| / 2 := h'
        _ = |(θ r - θ s + ((i : ℤ) - (j : ℤ) + 2 * m : ℤ)) / 2| := by rw [abs_div]; norm_num
        _ = _ := by congr 1; push_cast; ring
  have h := hCot (ι × Fin 2) t d w
    (fun r => div_pos (hpos r.1) (by norm_num))
    (fun r => by dsimp [d]; linarith [hunit r.1]) hspacing
  have hmass : (∑ r : ι × Fin 2, ‖w r‖ ^ 2 / d r) = 4 * ∑ r, ‖v r‖ ^ 2 / δ r := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp [w, d, Fin.sum_univ_two]
    ring
  have hform : (∑ r : ι × Fin 2, ∑ s : ι × Fin 2, if r = s then (0 : ℂ) else
      w r * conj (w s) * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((t r - t s : ℝ) : ℂ)))) =
      4 * ∑ r, ∑ s, if r = s then (0 : ℂ) else v r * conj (v s) *
        ((Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))⁻¹) := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hrs : r = s
    · subst s
      have h01 : (Real.pi : ℂ) * (((θ r / 2 + (0 : ℝ) / 2) - (θ r / 2 + (1 : ℝ) / 2) : ℝ) : ℂ) = -(Real.pi : ℂ) / 2 := by push_cast; ring
      have h10 : (Real.pi : ℂ) * (((θ r / 2 + (1 : ℝ) / 2) - (θ r / 2 + (0 : ℝ) / 2) : ℝ) : ℂ) = (Real.pi : ℂ) / 2 := by push_cast; ring
      simp [t, w, h01, h10, Complex.cot_eq_cos_div_sin, Complex.cos_neg, div_neg] <;> ring
    · have hz := sin_gap_ne_zero (θ r - θ s) (δ r) (hpos r) (hgap r s hrs)
      have hi := cot_double_lift ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)) hz
      have h00 : (Real.pi : ℂ) * (((θ r / 2 + (0 : ℝ) / 2) - (θ s / 2 + (0 : ℝ) / 2) : ℝ) : ℂ) = (Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ) / 2 := by push_cast; ring
      have h01 : (Real.pi : ℂ) * (((θ r / 2 + (0 : ℝ) / 2) - (θ s / 2 + (1 : ℝ) / 2) : ℝ) : ℂ) = (Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ) / 2 - (Real.pi : ℂ) / 2 := by push_cast; ring
      have h10 : (Real.pi : ℂ) * (((θ r / 2 + (1 : ℝ) / 2) - (θ s / 2 + (0 : ℝ) / 2) : ℝ) : ℂ) = (Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ) / 2 + (Real.pi : ℂ) / 2 := by push_cast; ring
      have h11 : (Real.pi : ℂ) * (((θ r / 2 + (1 : ℝ) / 2) - (θ s / 2 + (1 : ℝ) / 2) : ℝ) : ℂ) = (Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ) / 2 := by push_cast; ring
      norm_num at h00 h01 h10 h11
      norm_num [Prod.mk.injEq, hrs, w, t]
      push_cast at hi ⊢
      simp only [h00, h01, h10, h11]
      convert congrArg (fun q : ℂ => v r * conj (v s) * (Real.pi : ℂ) * q) hi using 1 <;> ring
  rw [hform, hmass, norm_mul] at h
  norm_num at h
  push_cast
  nlinarith only [h]

#print axioms solution

