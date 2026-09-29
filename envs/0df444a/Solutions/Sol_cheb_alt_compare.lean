-- Prove2me | solution 1 for cheb_alt_compare
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T12:35:31.392683+00:00
-- url     : https://prove2.me/submissions/5c483b4b-6789-4c19-b8d1-b21257138b3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_cheb_pythag
import Theorems.Thm_cheb_zeros_props
import Theorems.Thm_poly_alt_sign_compare
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

open Polynomial Polynomial.Chebyshev Real

theorem solution (p : Polynomial ℝ) {d : ℕ} (hd1 : 1 ≤ d) (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → Real.cos (Real.pi / (2 * (d : ℝ))) ≤ |c| →
      |p.eval c| ≤ |(Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c| := by
  intro c hc1 hc2 hcos
  have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpi := Real.pi_pos
  -- Chebyshev zeros: t j := cos((2j+1)π/(2d)) for j = 0..d-1.
  set t : ℕ → ℝ := fun j => Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * d)) with ht_def
  set Td' : Polynomial ℝ := derivative (T ℝ (d : ℤ)) with hTd'_def
  -- Step 0: argument range.
  have harg_bounds : ∀ j : ℕ, j ≤ d - 1 → (0 : ℝ) < (2 * (j : ℝ) + 1) * Real.pi / (2 * d)
      ∧ (2 * (j : ℝ) + 1) * Real.pi / (2 * d) < Real.pi := by
    intro j hj
    have hjd : j < d := by omega
    have hjr : (j : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hjd
    refine ⟨by positivity, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  -- Step 1: strict antimonotonicity of t on {0,...,d-1}.
  have ht_anti : ∀ i j : ℕ, i < j → j ≤ d - 1 → t j < t i := by
    intro i j hij hj
    have hi : i ≤ d - 1 := by omega
    have ⟨hib1, hib2⟩ := harg_bounds i hi
    have ⟨hjb1, hjb2⟩ := harg_bounds j hj
    apply Real.cos_lt_cos_of_nonneg_of_le_pi hib1.le hjb2.le
    have hir : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    rw [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 * (d : ℝ))]
    nlinarith [Real.pi_pos]
  -- Step 2: zeros and alternation properties.
  have hzeros : ∀ j : ℕ, j ≤ d - 1 →
      (T ℝ (d : ℤ)).eval (t j) = 0 ∧ 0 < (-1:ℝ)^j * Td'.eval (t j) ∧ -1 < t j ∧ t j < 1 := by
    intro j hj
    have hjd : j < d := by omega
    exact cheb_zeros_props d hd1 j hjd
  -- Step 3: natDegree bounds.
  have hTd'deg : Td'.natDegree ≤ d - 1 := by
    rw [hTd'_def]
    calc (derivative (T ℝ (d:ℤ))).natDegree ≤ (T ℝ (d:ℤ)).natDegree - 1 :=
          Polynomial.natDegree_derivative_le _
      _ = (d : ℤ).natAbs - 1 := by rw [natDegree_T]
      _ = d - 1 := by rw [Int.natAbs_natCast]
  have hpdeg : p.natDegree ≤ d - 1 := by omega
  -- Step 4: |p(t j)| ≤ |T'_d(t j)| from Bernstein hyp + Pythagoras.
  have hcmp : ∀ j : ℕ, j ≤ d - 1 → |p.eval (t j)| ≤ |Td'.eval (t j)| := by
    intro j hj
    obtain ⟨hTj0, hTd'j, htj1, htj2⟩ := hzeros j hj
    have h1tj : (0 : ℝ) < 1 - (t j)^2 := by nlinarith
    -- cheb_pythag at t j: (1-(t j)²)T'_d(t j)² + d²·T_d(t j)² = d², and T_d(t j)=0.
    have hpythag := cheb_pythag d (t j)
    rw [hTj0] at hpythag
    -- Bernstein hyp at t j: (1-(t j)²)p(t j)² ≤ d².
    have hbern := h (t j) htj1.le htj2.le
    -- So (p.eval (t j))² ≤ (T'_d.eval (t j))².
    have hsq : (p.eval (t j))^2 ≤ (Td'.eval (t j))^2 := by nlinarith
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h1
  -- Step 5: apply poly_alt_sign_compare.
  have hcmp_result := poly_alt_sign_compare Td' p (d - 1) t ht_anti hTd'deg hpdeg
    (fun j hj => (hzeros j hj).2.1) hcmp c
  -- Step 6: translate `cos(π/(2d)) ≤ |c|` into `t 0 ≤ c ∨ c ≤ t (d-1)`.
  have ht0 : t 0 = Real.cos (Real.pi / (2 * (d : ℝ))) := by
    rw [ht_def]
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
  have htd1 : t (d - 1) = -Real.cos (Real.pi / (2 * (d : ℝ))) := by
    rw [ht_def]
    have hd1r : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have := Nat.cast_sub hd1 (R := ℝ)
      push_cast at this ⊢
      linarith
    simp only
    rw [hd1r]
    have harg : (2 * ((d : ℝ) - 1) + 1) * Real.pi / (2 * d) = Real.pi - Real.pi / (2 * d) := by
      field_simp
      ring
    rw [harg, Real.cos_pi_sub]
  have hdisj : t 0 ≤ c ∨ c ≤ t (d - 1) := by
    rw [ht0, htd1]
    rcases le_abs.mp hcos with hle | hle
    · left; exact hle
    · right; linarith
  exact hcmp_result hdisj
