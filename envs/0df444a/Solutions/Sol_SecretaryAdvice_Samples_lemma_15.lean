-- Prove2me | solution 1 for SecretaryAdvice.Samples.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:20:29.000096+00:00
-- url     : https://prove2.me/submissions/634959a7-eb4e-48be-9427-a17259ac65a0

import Mathlib
set_option autoImplicit false
open Finset

lemma sec15_key (a b : ℤ) (hab : a < b) (s : ℤ) :
    ∏ t ∈ Icc a b, ((s + 1 + t : ℤ) : ℝ) - ∏ t ∈ Icc a b, ((s + t : ℤ) : ℝ) =
      ((b - a + 1 : ℤ) : ℝ) * ∏ t ∈ Icc (a + 1) b, ((s + t : ℤ) : ℝ) := by
  have h1 : Icc a b = insert a (Icc (a + 1) b) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  have h2 : ∏ t ∈ Icc a b, ((s + 1 + t : ℤ) : ℝ) =
      ∏ t ∈ Icc (a + 1) (b + 1), ((s + t : ℤ) : ℝ) := by
    have : Icc (a + 1) (b + 1) = (Icc a b).image (fun t => t + 1) := by
      ext x; simp only [mem_Icc, mem_image]
      constructor
      · intro h; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨y, hy, rfl⟩; omega
    rw [this, Finset.prod_image (fun x _ y _ h => by simpa using h)]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    push_cast; ring_nf
  have h3 : Icc (a + 1) (b + 1) = insert (b + 1) (Icc (a + 1) b) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  rw [h2, h3, Finset.prod_insert (by simp), h1, Finset.prod_insert (by simp)]
  have h4 : (a + 1 : ℤ) ∈ Icc (a+1) b := by simp; omega
  push_cast
  ring

theorem solution (a b u v : ℤ) (hab : a < b) (huv : u < v) :
    ∑ s ∈ Icc u v, ∏ t ∈ Icc (a + 1) b, ((s + t : ℤ) : ℝ) =
      1 / ((b - a + 1 : ℤ) : ℝ) *
        (∏ t ∈ Icc a b, ((v + 1 + t : ℤ) : ℝ) - ∏ t ∈ Icc a b, ((u + t : ℤ) : ℝ)) := by
  have hc : ((b - a + 1 : ℤ) : ℝ) ≠ 0 := by
    have : (0 : ℤ) < b - a + 1 := by omega
    exact_mod_cast this.ne'
  have main : ∀ w : ℤ, u ≤ w →
      ∑ s ∈ Icc u w, ∏ t ∈ Icc (a + 1) b, ((s + t : ℤ) : ℝ) =
      1 / ((b - a + 1 : ℤ) : ℝ) *
        (∏ t ∈ Icc a b, ((w + 1 + t : ℤ) : ℝ) - ∏ t ∈ Icc a b, ((u + t : ℤ) : ℝ)) := by
    intro w hw
    induction w, hw using Int.le_induction with
    | base =>
      rw [Icc_self, sum_singleton]
      have := sec15_key a b hab u
      field_simp
      linarith
    | succ w hw ih =>
      have : Icc u (w + 1) = insert (w + 1) (Icc u w) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [this, sum_insert (by simp), ih]
      have := sec15_key a b hab (w + 1)
      have e : ∀ t : ℤ, w + 1 + 1 + t = (w + 1) + 1 + t := fun t => rfl
      field_simp
      linarith
  exact main v huv.le
