-- Prove2me | solution 1 for WeightedCoordGames.count_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:12:07.510772+00:00
-- url     : https://prove2.me/submissions/f96c36d1-cccc-4de2-8bb4-fa8260d9736a

import Mathlib

namespace Aux_WCG_cube

theorem gauss2 (n : ℕ) : (∑ x ∈ Finset.Icc 1 n, x) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    ring

theorem gauss (n : ℕ) : ∑ x ∈ Finset.Icc 1 n, x = n * (n + 1) / 2 :=
  (Nat.div_eq_of_eq_mul_left (by norm_num) (gauss2 n).symm).symm

theorem half2 (x : ℕ) : x * (1 + x) / 2 * 2 = x * (1 + x) := by
  rw [show 1 + x = x + 1 by ring]
  exact Nat.div_mul_cancel (Nat.even_mul_succ_self x).two_dvd

theorem tetra6 (m : ℕ) : (∑ x ∈ Finset.Icc 1 m, x * (1 + x) / 2) * 6 = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    have ht := half2 (m + 1)
    nlinarith [ht]

theorem inner (m g : ℕ) (hg : g < m) :
    ∑ p ∈ Finset.Icc (g + 1) m, (p - g) = (m - g) * (1 + m - g) / 2 := by
  have h : ∑ p ∈ Finset.Icc (g + 1) m, (p - g) = ∑ x ∈ Finset.Icc 1 (m - g), x := by
    apply Finset.sum_nbij' (fun p => p - g) (fun x => x + g)
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
    · intro a _; rfl
  rw [h, gauss, show 1 + m - g = m - g + 1 by omega]

theorem reflect (m : ℕ) (f : ℕ → ℕ) :
    ∑ g ∈ Finset.range m, f (m - g) = ∑ x ∈ Finset.Icc 1 m, f x := by
  apply Finset.sum_nbij' (fun g => m - g) (fun x => m - x)
  · intro a ha; simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_range] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a _; rfl

end Aux_WCG_cube

theorem solution (m : ℕ) (hm : 2 ≤ m) :
    1 + (∑ g ∈ Finset.range m, ∑ p ∈ Finset.Icc (g + 1) m, (p - g)) +
          (∑ g ∈ Finset.range m, (m - g)) =
        1 + (∑ g ∈ Finset.range m, (m - g) * (1 + m - g) / 2) + m * (1 + m) / 2 ∧
    1 + (∑ g ∈ Finset.range m, (m - g) * (1 + m - g) / 2) + m * (1 + m) / 2 =
        1 + (∑ x ∈ Finset.Icc 1 m, x * (1 + x) / 2) + m * (1 + m) / 2 ∧
    1 + (∑ x ∈ Finset.Icc 1 m, x * (1 + x) / 2) + m * (1 + m) / 2 =
        1 + m * (m + 1) * (m + 2) / 6 + m * (1 + m) / 2 ∧
    1 + m * (m + 1) * (m + 2) / 6 + m * (1 + m) / 2 = 1 + m * (m + 1) * (m + 5) / 6 ∧
    1 + m * (m + 1) * (m + 5) / 6 ≤ m ^ 3 := by
  have hT : ∑ x ∈ Finset.Icc 1 m, x * (1 + x) / 2 = m * (m + 1) * (m + 2) / 6 :=
    (Nat.div_eq_of_eq_mul_left (by norm_num) (Aux_WCG_cube.tetra6 m).symm).symm
  have hB : m * (1 + m) / 2 * 2 = m * (1 + m) := Aux_WCG_cube.half2 m
  have hA : m * (m + 1) * (m + 2) / 6 * 6 = m * (m + 1) * (m + 2) := by
    rw [← hT]; exact Aux_WCG_cube.tetra6 m
  have hC : m * (m + 1) * (m + 5) / 6 = m * (m + 1) * (m + 2) / 6 + m * (1 + m) / 2 := by
    apply Nat.div_eq_of_eq_mul_left (by norm_num)
    nlinarith [hA, hB]
  refine ⟨?_, ?_, by rw [hT], by rw [hC, add_assoc], ?_⟩
  · congr 1
    · congr 1
      exact Finset.sum_congr rfl (fun g hg => Aux_WCG_cube.inner m g (Finset.mem_range.mp hg))
    · rw [Aux_WCG_cube.reflect m (fun x => x), Aux_WCG_cube.gauss, add_comm 1 m]
  · congr 2
    rw [← Aux_WCG_cube.reflect m (fun x => x * (1 + x) / 2)]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    have := Finset.mem_range.mp hg
    rw [show 1 + m - g = 1 + (m - g) by omega]
  · rw [hC]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    nlinarith [hA, hB, Nat.zero_le (k * k * k), Nat.zero_le (k * k), Nat.zero_le k]
