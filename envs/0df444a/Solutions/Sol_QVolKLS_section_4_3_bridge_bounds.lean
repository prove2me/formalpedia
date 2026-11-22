-- Prove2me | solution 1 for QVolKLS.section_4_3_bridge_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T14:46:50.815845+00:00
-- url     : https://prove2.me/submissions/e24b3e26-8f6a-4a79-bda8-11fdeef0d165

import Mathlib

set_option autoImplicit false

theorem solution {Ω : Type*} [Fintype Ω] (π π' X : Ω → ℝ) (c : ℝ)
    (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1) (hX : ∀ x, 0 < X x)
    (h30 : ∀ x, π' x = X x / (∑ y, π y * X y) * π x)
    (h31 : ∑ x, π x * (X x / ∑ y, π y * X y) ^ 2 ≤ 4)
    (hc : (∑ y, π y * X y) / 2 ≤ c ∧ c ≤ 2 * ∑ y, π y * X y) :
    (∑ x, π' x * (c / (c + X x))) = c / (∑ y, π y * X y) * ∑ x, π x * (X x / (c + X x)) ∧
    (∑ y, π y * X y) = c * (∑ x, π x * (X x / (c + X x))) / (∑ x, π' x * (c / (c + X x))) ∧
    1 / 6 ≤ ∑ x, π x * (X x / (c + X x)) ∧
    1 / 9 ≤ ∑ x, π' x * (c / (c + X x)) := by
  classical
  let μ : ℝ := ∑ y, π y * X y
  have hπ_exists : ∃ x0, 0 < π x0 := by
    by_contra h
    push_neg at h
    have hzero : ∀ x, π x = 0 := fun x => le_antisymm (h x) (hπ x)
    have hsum0 : (∑ x, π x) = 0 := by simp [hzero]
    rw [hπ1] at hsum0
    norm_num at hsum0
  obtain ⟨x0, hx0⟩ := hπ_exists
  have hμpos : 0 < μ := by
    have hterm : 0 < π x0 * X x0 := mul_pos hx0 (hX x0)
    have hle : π x0 * X x0 ≤ ∑ x, π x * X x :=
      Finset.single_le_sum (fun x _ => mul_nonneg (hπ x) (hX x).le) (Finset.mem_univ x0)
    exact lt_of_lt_of_le hterm hle
  have hcpos : 0 < c := by linarith [hc.1, hμpos]
  let t : ℝ := c / μ
  have htpos : 0 < t := div_pos hcpos hμpos
  have ht_lower : (1 : ℝ) / 2 ≤ t := by
    rw [show t = c / μ from rfl, le_div_iff₀ hμpos]
    linarith [hc.1]
  have ht_upper : t ≤ 2 := by
    rw [show t = c / μ from rfl, div_le_iff₀ hμpos]
    linarith [hc.2]
  have hYpos : ∀ x, 0 < X x / μ := fun x => div_pos (hX x) hμpos
  -- ratio identities
  have hcX : ∀ x, c / (c + X x) = t / (t + X x / μ) := by
    intro x
    have hcx : c + X x ≠ 0 := by
      have : 0 < c + X x := by linarith [hcpos, hX x]
      exact this.ne'
    have hty : t + X x / μ ≠ 0 := by
      have h : 0 < X x / μ := div_pos (hX x) hμpos
      have : 0 < t + X x / μ := by linarith
      exact this.ne'
    rw [show t = c / μ from rfl]
    field_simp [hcx, hty, hμpos.ne']
  have hXX : ∀ x, X x / (c + X x) = (X x / μ) / (t + X x / μ) := by
    intro x
    have hcx : c + X x ≠ 0 := by
      have : 0 < c + X x := by linarith [hcpos, hX x]
      exact this.ne'
    have hty : t + X x / μ ≠ 0 := by
      have h : 0 < X x / μ := div_pos (hX x) hμpos
      have : 0 < t + X x / μ := by linarith
      exact this.ne'
    rw [show t = c / μ from rfl]
    field_simp [hcx, hty, hμpos.ne']
  -- pointwise identity and inequality
  have hpoint_eq : ∀ y : ℝ, 0 < y →
      y / (t + y) = ((t + 8) / (t + 4) ^ 2) * y - (1 / (t + 4) ^ 2) * y ^ 2
        + y * (y - 4) ^ 2 / ((t + y) * (t + 4) ^ 2) := by
    intro y hy
    have hty : t + y ≠ 0 := by positivity
    have ht4 : t + 4 ≠ 0 := by positivity
    field_simp [hty, ht4]
    ring
  have hpoint_le : ∀ y : ℝ, 0 < y →
      ((t + 8) / (t + 4) ^ 2) * y - (1 / (t + 4) ^ 2) * y ^ 2 ≤ y / (t + y) := by
    intro y hy
    have hnonneg : 0 ≤ y * (y - 4) ^ 2 / ((t + y) * (t + 4) ^ 2) := by positivity
    linarith [hpoint_eq y hy]
  let A : ℝ := ∑ x, π x * (X x / (c + X x))
  let B : ℝ := ∑ x, π' x * (c / (c + X x))
  -- sum of Y
  have hYsum : ∑ x, π x * (X x / μ) = 1 := by
    have h : ∑ x, π x * (X x / μ) = (∑ x, π x * X x) / μ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h, div_self hμpos.ne']
  have hY2sum : ∑ x, π x * (X x / μ) ^ 2 ≤ 4 := h31
  -- A lower bound
  have hA_lower : ((t + 8) / (t + 4) ^ 2) * (∑ x, π x * (X x / μ))
      - (1 / (t + 4) ^ 2) * (∑ x, π x * (X x / μ) ^ 2) ≤ A := by
    calc ((t + 8) / (t + 4) ^ 2) * (∑ x, π x * (X x / μ))
          - (1 / (t + 4) ^ 2) * (∑ x, π x * (X x / μ) ^ 2)
        = ∑ x, π x * (((t + 8) / (t + 4) ^ 2) * (X x / μ)
            - (1 / (t + 4) ^ 2) * (X x / μ) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ ≤ ∑ x, π x * ((X x / μ) / (t + X x / μ)) := by
            apply Finset.sum_le_sum
            intro x _
            exact mul_le_mul_of_nonneg_left (hpoint_le (X x / μ) (hYpos x)) (hπ x)
      _ = A := by
            change (∑ x, π x * ((X x / μ) / (t + X x / μ)))
                = ∑ x, π x * (X x / (c + X x))
            apply Finset.sum_congr rfl
            intro x _
            rw [← hXX x]
  have hA_ge_t : 1 / (t + 4) ≤ A := by
    have h1 : ((t + 8) / (t + 4) ^ 2) * 1 - (1 / (t + 4) ^ 2) * 4 = 1 / (t + 4) := by
      field_simp
      ring
    have h2 : ((t + 8) / (t + 4) ^ 2) * 1 - (1 / (t + 4) ^ 2) * 4 ≤ A := by
      have hlow := hA_lower
      rw [hYsum] at hlow
      have hD : 0 ≤ 1 / (t + 4) ^ 2 := by positivity
      have hmul : (1 / (t + 4) ^ 2) * (∑ x, π x * (X x / μ) ^ 2)
          ≤ (1 / (t + 4) ^ 2) * 4 := mul_le_mul_of_nonneg_left hY2sum hD
      linarith
    linarith
  have hA_ge : (1 : ℝ) / 6 ≤ A := by
    have ht4le : t + 4 ≤ 6 := by linarith
    have h : (1 : ℝ) / 6 ≤ 1 / (t + 4) :=
      one_div_le_one_div_of_le (by linarith : 0 < t + 4) ht4le
    linarith
  -- B = t * A
  have hB_eq : B = t * A := by
    change (∑ x, π' x * (c / (c + X x))) = t * (∑ x, π x * (X x / (c + X x)))
    calc ∑ x, π' x * (c / (c + X x))
        = ∑ x, (X x / μ * π x) * (t / (t + X x / μ)) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [h30 x, hcX x]
      _ = t * ∑ x, π x * ((X x / μ) / (t + X x / μ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = t * (∑ x, π x * (X x / (c + X x))) := by
            congr 1
            change (∑ x, π x * ((X x / μ) / (t + X x / μ)))
                = ∑ x, π x * (X x / (c + X x))
            apply Finset.sum_congr rfl
            intro x _
            rw [← hXX x]
  have hB_ge : (1 : ℝ) / 9 ≤ B := by
    rw [hB_eq]
    have h1 : (1 : ℝ) / 9 ≤ t / (t + 4) := by
      rw [le_div_iff₀ (by linarith : 0 < t + 4)]
      nlinarith [ht_lower]
    have h2 : t / (t + 4) ≤ t * (1 / (t + 4)) := by
      ring_nf
      exact le_rfl
    have h3 : t * (1 / (t + 4)) ≤ t * A := mul_le_mul_of_nonneg_left hA_ge_t htpos.le
    linarith
  -- the two equalities
  have hEq1 : (∑ x, π' x * (c / (c + X x))) =
      c / μ * ∑ x, π x * (X x / (c + X x)) := by
    change (∑ x, π' x * (c / (c + X x))) =
      t * (∑ x, π x * (X x / (c + X x)))
    exact hB_eq
  have hEq2 : μ = c * A / B := by
    have hBpos : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 9) hB_ge
    have hApos : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 6) hA_ge
    rw [hB_eq, show t = c / μ from rfl]
    field_simp
  exact ⟨hEq1, hEq2, hA_ge, hB_ge⟩

