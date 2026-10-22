-- Prove2me | solution 1 for RelSmoothFOM.PrimalGrad.ck_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:35:26.130336+00:00
-- url     : https://prove2.me/submissions/ad90a297-922e-4a99-83a9-1c4e732f3c2e

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

set_option autoImplicit false

theorem geom_aux (r : ℝ) (k : ℕ) :
    (r - 1) * ∑ i ∈ Finset.Icc 1 k, r ^ i = r ^ (k + 1) - r := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

theorem solution (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ < L)
    (k : ℕ) (hk : 1 ≤ k) :
    (0 < μ → 1 / ∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i
        = μ / (L * ((1 + μ / (L - μ)) ^ k - 1))) ∧
    (μ = 0 → 1 / ∑ i ∈ Finset.Icc 1 k, (L / (L - μ)) ^ i = 1 / (k : ℝ)) := by
  have hLμ : 0 < L - μ := by linarith
  refine ⟨fun hpos => ?_, fun h0 => ?_⟩
  · have hr1' : 1 + μ / (L - μ) = L / (L - μ) := by
      field_simp <;> ring
    rw [hr1']
    generalize hr : L / (L - μ) = r
    have hr1 : r - 1 = μ / (L - μ) := by
      rw [← hr]; field_simp <;> ring
    have hrgt : 1 < r := by
      have : 0 < μ / (L - μ) := by positivity
      linarith
    have hrk : 1 < r ^ k := one_lt_pow₀ hrgt (by omega)
    have hne : r - 1 ≠ 0 := by linarith
    have hX : r ^ k - 1 ≠ 0 := by linarith
    have hsum := geom_aux r k
    have hS : ∑ i ∈ Finset.Icc 1 k, r ^ i = r * (r ^ k - 1) / (r - 1) := by
      rw [eq_div_iff hne]
      rw [mul_comm, hsum]; ring
    rw [hS, one_div_div]
    have hrpos : r ≠ 0 := by linarith
    have hL' : L ≠ 0 := hL.ne'
    rw [div_eq_div_iff (mul_ne_zero hrpos hX) (mul_ne_zero hL' hX)]
    calc (r - 1) * (L * (r ^ k - 1)) = μ / (L - μ) * (L * (r ^ k - 1)) := by rw [hr1]
      _ = μ * (L / (L - μ) * (r ^ k - 1)) := by ring
      _ = μ * (r * (r ^ k - 1)) := by rw [hr]
  · subst h0
    simp [div_self hL.ne']
