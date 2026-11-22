-- Prove2me | solution 1 for Pseudorandom.coord_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:03.662795+00:00
-- url     : https://prove2.me/submissions/c99b006a-a10e-4b2b-b570-79e2c3fc83ba

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Theorems.Thm_Pseudorandom_exp_le_one_add_add_sq_div

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
namespace Pseudorandom
theorem _root_.solution {α : Type*} [Fintype α] (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (M : α → ℝ) (c L lam q : ℝ) (R : Finset α)
    (hgap : ∀ a b, |M a - M b| ≤ c) (hR : ∀ a b, a ∉ R → b ∉ R → M a = M b)
    (hq : ∑ a ∈ R, p a ≤ q) (hcL : c ≤ L) (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    ∑ a, p a * Real.exp (lam * (M a - ∑ b, p b * M b)) ≤
      Real.exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L))) := by
  classical
  set m := ∑ b, p b * M b with hm
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hp1
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hgap (Classical.arbitrary _) (Classical.arbitrary _))
  have hY : ∀ a, |M a - m| ≤ c := by
    intro a
    have : M a - m = ∑ b, p b * (M a - M b) := by
      rw [hm]; simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul]
    rw [this]
    calc |∑ b, p b * (M a - M b)| ≤ ∑ b, |p b * (M a - M b)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ b, p b * c := sum_le_sum fun b _ => by
          rw [abs_mul, abs_of_nonneg (hp0 b)]
          exact mul_le_mul_of_nonneg_left (hgap a b) (hp0 b)
      _ = c := by rw [← sum_mul, hp1, one_mul]
  have hK : 0 < 1 - lam * L := by linarith
  -- variance bound
  have hvar : ∑ a, p a * (M a - m) ^ 2 ≤ q * c ^ 2 := by
    have hdecomp : ∀ x : ℝ, ∑ a, p a * (M a - x) ^ 2 =
        ∑ a, p a * (M a - m) ^ 2 + (m - x) ^ 2 := by
      intro x
      have h0 : ∑ a, p a * (M a - m) = 0 := by
        simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul, hm]; ring
      have : ∀ a, p a * (M a - x) ^ 2 =
          p a * (M a - m) ^ 2 + 2 * (m - x) * (p a * (M a - m)) + (m - x) ^ 2 * p a := by
        intro a; ring
      simp_rw [this]
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, h0, ← mul_sum, hp1]; ring
    by_cases hex : ∃ b0, b0 ∉ R
    · obtain ⟨b0, hb0⟩ := hex
      have := hdecomp (M b0)
      calc ∑ a, p a * (M a - m) ^ 2 ≤ ∑ a, p a * (M a - M b0) ^ 2 := by
            rw [this]; nlinarith [sq_nonneg (m - M b0)]
        _ ≤ ∑ a, if a ∈ R then p a * c ^ 2 else 0 := by
            refine sum_le_sum fun a _ => ?_
            split_ifs with ha
            · apply mul_le_mul_of_nonneg_left _ (hp0 a)
              have := hgap a b0
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
            · rw [hR a b0 ha hb0]; simp
        _ = (∑ a ∈ R, p a) * c ^ 2 := by
            rw [← sum_filter, sum_mul]; simp
        _ ≤ q * c ^ 2 := mul_le_mul_of_nonneg_right hq (sq_nonneg c)
    · push_neg at hex
      have hR1 : ∑ a ∈ R, p a = 1 := by
        rw [← hp1]; congr 1; ext a; simp [hex a]
      calc ∑ a, p a * (M a - m) ^ 2 ≤ ∑ a, p a * c ^ 2 := sum_le_sum fun a _ => by
            apply mul_le_mul_of_nonneg_left _ (hp0 a)
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hY a) 2
        _ = c ^ 2 := by rw [← sum_mul, hp1, one_mul]
        _ ≤ q * c ^ 2 := by
            have : 1 ≤ q := hR1 ▸ hq
            nlinarith [sq_nonneg c]
  have hpt : ∀ a, Real.exp (lam * (M a - m)) ≤
      1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L)) := by
    intro a
    apply exp_le_one_add_add_sq_div _ _ _ hlamL
    rw [abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left ((hY a).trans hcL) hlam
  calc ∑ a, p a * Real.exp (lam * (M a - m))
      ≤ ∑ a, p a * (1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L))) :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hp0 a)
    _ = 1 + lam * ∑ a, p a * (M a - m) +
          lam ^ 2 / (2 * (1 - lam * L)) * ∑ a, p a * (M a - m) ^ 2 := by
        have : ∀ a, p a * (1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L)))
            = p a + lam * (p a * (M a - m)) +
              lam ^ 2 / (2 * (1 - lam * L)) * (p a * (M a - m) ^ 2) := by
          intro a; ring
        simp_rw [this]
        rw [sum_add_distrib, sum_add_distrib, hp1, ← mul_sum, ← mul_sum]
    _ = 1 + lam ^ 2 / (2 * (1 - lam * L)) * ∑ a, p a * (M a - m) ^ 2 := by
        have h0 : ∑ a, p a * (M a - m) = 0 := by
          simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul, hm]; ring
        rw [h0]; ring
    _ ≤ 1 + lam ^ 2 / (2 * (1 - lam * L)) * (q * c ^ 2) := by
        gcongr
    _ ≤ Real.exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L))) := by
        have := Real.add_one_le_exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L)))
        rw [div_mul_eq_mul_div] at *
        linarith
end Pseudorandom
