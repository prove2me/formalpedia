-- Prove2me | solution 1 for RobustLP.Counterpart.alpha_beta_ratio
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:25:20.111093+00:00
-- url     : https://prove2.me/submissions/b38613cb-bebc-43dc-9a58-da3c9a227975

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
open scoped BigOperators

namespace RobustLP.Counterpart

/-- **The ratio `α_i/β_i`** (Ben-Tal–Nemirovski 2000, §3.1, p. 420), corrected for the factor `Ω`.
With `α_i(x) = ∑_{j ∈ J_i} |a_{ij}| |x_j|` and `β_i(x) = Ω √(∑_{j ∈ J_i} a_{ij}² x_j²)`, `Ω > 0`:
(a) `Ω α_i(x) ≤ √card(J_i) · β_i(x)` for every `x`, and
(b) if `J_i` is nonempty and `a_{ij} ≠ 0` for every `j ∈ J_i`, some `x` has `β_i(x) > 0` and
`Ω α_i(x) = √card(J_i) · β_i(x)`.
So the largest value of `α_i/β_i` is `√card(J_i)/Ω` (the page prints `√card(J_i)`). -/
theorem _root_.solution {n p m : ℕ} (L : UncertainLP n p m) (Ω : ℝ) (hΩ : 0 < Ω)
    (i : Fin m) :
    (∀ x : Fin n → ℝ,
      Ω * ∑ j ∈ L.J i, |L.A i j| * |x j| ≤
        Real.sqrt ((L.J i).card) * (Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2))) ∧
    ((L.J i).Nonempty → (∀ j ∈ L.J i, L.A i j ≠ 0) →
      ∃ x : Fin n → ℝ, 0 < Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2) ∧
        Ω * ∑ j ∈ L.J i, |L.A i j| * |x j| =
          Real.sqrt ((L.J i).card) * (Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2))) := by
  classical
  constructor
  · intro x
    let S : ℝ := ∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2
    have hS : 0 ≤ S := Finset.sum_nonneg fun j hj => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hcard : 0 ≤ ((L.J i).card : ℝ) := Nat.cast_nonneg _
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (L.J i) (fun _ => (1 : ℝ))
      (fun j => |L.A i j| * |x j|)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_pow,
      sq_abs] at hCS
    have hsqrt := Real.sq_sqrt hS
    have hcsqrt := Real.sq_sqrt hcard
    have hb : (∑ j ∈ L.J i, |L.A i j| * |x j|) ≤ Real.sqrt ((L.J i).card) * Real.sqrt S := by
      have hprod := mul_nonneg (Real.sqrt_nonneg ((L.J i).card : ℝ)) (Real.sqrt_nonneg S)
      have hsq : (Real.sqrt ((L.J i).card) * Real.sqrt S) ^ 2 = ((L.J i).card : ℝ) * S := by
        rw [mul_pow, hcsqrt, hsqrt]
      dsimp [S] at *
      nlinarith
    have := mul_le_mul_of_nonneg_left hb hΩ.le
    dsimp [S] at this
    nlinarith
  · intro hne hA
    refine ⟨fun j => (L.A i j)⁻¹, ?_, ?_⟩
    have hs : (∑ j ∈ L.J i, L.A i j ^ 2 * (L.A i j)⁻¹ ^ 2) = ((L.J i).card : ℝ) := by
      calc
        _ = ∑ j ∈ L.J i, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← mul_pow, mul_inv_cancel₀ (hA j hj), one_pow]
        _ = _ := by simp
    have hp : 0 < ((L.J i).card : ℝ) := Nat.cast_pos.mpr hne.card_pos
    rw [hs]
    exact mul_pos hΩ (Real.sqrt_pos.mpr hp)
    have hs : (∑ j ∈ L.J i, L.A i j ^ 2 * (L.A i j)⁻¹ ^ 2) = ((L.J i).card : ℝ) := by
      calc
        _ = ∑ j ∈ L.J i, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← mul_pow, mul_inv_cancel₀ (hA j hj), one_pow]
        _ = _ := by simp
    have ha : (∑ j ∈ L.J i, |L.A i j| * |(L.A i j)⁻¹|) = ((L.J i).card : ℝ) := by
      calc
        _ = ∑ j ∈ L.J i, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← abs_mul, mul_inv_cancel₀ (hA j hj), abs_one]
        _ = _ := by simp
    rw [hs, ha]
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (L.J i).card : 0 ≤ ((L.J i).card : ℝ))]


end RobustLP.Counterpart
