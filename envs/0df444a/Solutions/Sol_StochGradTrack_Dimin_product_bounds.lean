-- Prove2me | solution 1 for StochGradTrack.Dimin.product_bounds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:06:34.167222+00:00
-- url     : https://prove2.me/submissions/9a337b03-e9e7-43aa-961d-64f1c687cfe6

import Mathlib
set_option autoImplicit false

lemma oo_step (c w : ℝ) (hc : 0 ≤ c) (hw : 0 < w) :
    1 - c / w ≤ (w / (w + 1)) ^ c := by
  have h1 : Real.log (1 + 1 / w) ≤ 1 / w := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / w by positivity)
    linarith
  have h2 : (w / (w + 1)) ^ c = Real.exp (-(c * Real.log (1 + 1 / w))) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    have : w / (w + 1) = (1 + 1 / w)⁻¹ := by field_simp
    rw [this, Real.log_inv]; ring_nf
  rw [h2]
  have h3 : -(c / w) ≤ -(c * Real.log (1 + 1 / w)) := by
    have := mul_le_mul_of_nonneg_left h1 hc
    have e : c * (1 / w) = c / w := by ring
    linarith
  calc 1 - c / w ≤ Real.exp (-(c / w)) := by
        have := Real.add_one_le_exp (-(c / w)); linarith
    _ ≤ _ := Real.exp_le_exp.2 h3

lemma oo_prod (c u : ℝ) (hc : 0 ≤ c) (hcu : c ≤ u) (hu : 0 < u) (n : ℕ) :
    ∏ j ∈ Finset.range n, (1 - c / (u + j)) ≤ (u / (u + n)) ^ c := by
  induction n with
  | zero => simp [div_self hu.ne']
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have hw : 0 < u + n := by positivity
    have hf : 0 ≤ 1 - c / (u + n) := by
      rw [sub_nonneg, div_le_one hw]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hA : 0 ≤ (u / (u + n)) ^ c := by positivity
    calc (∏ j ∈ Finset.range n, (1 - c / (u + j))) * (1 - c / (u + n))
        ≤ (u / (u + n)) ^ c * (1 - c / (u + n)) := mul_le_mul_of_nonneg_right ih hf
      _ ≤ (u / (u + n)) ^ c * ((u + n) / (u + n + 1)) ^ c :=
          mul_le_mul_of_nonneg_left (oo_step c _ hc hw) hA
      _ = (u / (u + ↑(n + 1))) ^ c := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          congr 1
          push_cast
          rw [show u + ((n : ℝ) + 1) = u + n + 1 by ring]
          have : u + (n : ℝ) + 1 ≠ 0 := by positivity
          field_simp

theorem solution (θ μ m : ℝ) (h0 : 0 ≤ θ * μ) (hle : θ * μ ≤ m) (hm : 0 < m) (k : ℕ) :
    ∏ t ∈ Finset.range k, (1 - θ * μ / (m + t)) ≤ m ^ (θ * μ) / (m + k) ^ (θ * μ) ∧
    ∀ t : ℕ, t < k →
      ∏ j ∈ Finset.Ico (t + 1) k, (1 - θ * μ / (m + j)) ≤ (m + t + 1) ^ (θ * μ) / (m + k) ^ (θ * μ) := by
  constructor
  · have := oo_prod (θ * μ) m h0 hle hm k
    rwa [Real.div_rpow hm.le (by positivity)] at this
  · intro t ht
    rw [Finset.prod_Ico_eq_prod_range]
    have hu : 0 < m + t + 1 := by positivity
    have hcu : θ * μ ≤ m + t + 1 := by
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith
    have := oo_prod (θ * μ) (m + t + 1) h0 hcu hu (k - (t + 1))
    have e1 : ((m + t + 1) + ((k - (t + 1) : ℕ) : ℝ)) = m + k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, Real.div_rpow hu.le (by positivity)] at this
    refine le_of_eq_of_le ?_ this
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring_nf
