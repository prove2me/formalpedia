-- Prove2me | solution 1 for TaoFivePrimes.vinogradov_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T01:38:39.441428+00:00
-- url     : https://prove2.me/submissions/eac9eb7c-1815-4290-ae8d-b1b7f97b0f66

import Mathlib

open Finset

section PartVino
open Finset
namespace TaoVino

/-- Summing a nonnegative function over `k` consecutive blocks of length `q`. -/
theorem blocks_le (q : ℕ) (hq : 0 < q) (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (C : ℝ) (hC : ∀ m : ℤ, (∑ n ∈ Finset.Ioc m (m + (q : ℤ)), f n) ≤ C) :
    ∀ (k : ℕ) (m : ℤ), (∑ n ∈ Finset.Ioc m (m + (k : ℤ) * q), f n) ≤ (k : ℝ) * C := by
  intro k
  induction k with
  | zero => intro m; simp
  | succ k ih =>
      intro m
      have hqz : (0 : ℤ) ≤ (q : ℤ) := by positivity
      have hle1 : m ≤ m + (k : ℤ) * q := by nlinarith [Int.natCast_nonneg k]
      have hshape : m + ((k : ℕ) + 1 : ℤ) * q = (m + (k : ℤ) * q) + (q : ℤ) := by ring
      have hle2 : m + (k : ℤ) * q ≤ (m + (k : ℤ) * q) + (q : ℤ) := by linarith
      have hdisj : Disjoint (Finset.Ioc m (m + (k : ℤ) * q))
          (Finset.Ioc (m + (k : ℤ) * q) ((m + (k : ℤ) * q) + (q : ℤ))) := by
        rw [Finset.disjoint_left]
        intro n hn hn'
        rw [Finset.mem_Ioc] at hn hn'
        omega
      have hunion : Finset.Ioc m (m + (k : ℤ) * q)
          ∪ Finset.Ioc (m + (k : ℤ) * q) ((m + (k : ℤ) * q) + (q : ℤ))
          = Finset.Ioc m ((m + (k : ℤ) * q) + (q : ℤ)) :=
        Finset.Ioc_union_Ioc_eq_Ioc hle1 hle2
      have hsplit : (∑ n ∈ Finset.Ioc m ((m + (k : ℤ) * q) + (q : ℤ)), f n)
          = (∑ n ∈ Finset.Ioc m (m + (k : ℤ) * q), f n)
            + ∑ n ∈ Finset.Ioc (m + (k : ℤ) * q) ((m + (k : ℤ) * q) + (q : ℤ)), f n := by
        rw [← hunion, Finset.sum_union hdisj]
      have h1 := ih m
      have h2 := hC (m + (k : ℤ) * q)
      have hgoal : (∑ n ∈ Finset.Ioc m (m + ((k : ℕ) + 1 : ℤ) * q), f n)
          ≤ ((k : ℝ) + 1) * C := by
        rw [hshape, hsplit]
        nlinarith [h1, h2]
      have hcast : ((k + 1 : ℕ) : ℤ) * (q : ℤ) = ((k : ℕ) + 1 : ℤ) * (q : ℤ) := by push_cast; ring
      calc (∑ n ∈ Finset.Ioc m (m + ((k + 1 : ℕ) : ℤ) * q), f n)
          = ∑ n ∈ Finset.Ioc m (m + ((k : ℕ) + 1 : ℤ) * q), f n := by rw [hcast]
        _ ≤ ((k : ℝ) + 1) * C := hgoal
        _ = ((k + 1 : ℕ) : ℝ) * C := by push_cast; ring

/-- **Tao, Lemma 3.4 (Vinogradov-type lemma)**, deduced by subdivision from the
single-block estimate. -/
theorem vinogradov (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (halpha : alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (theta x y : ℝ) (hxy : x < y)
    (hblock : ∀ (A' theta' : ℝ), 0 < A' → ∀ m : ℤ,
      (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
          min A' (1 / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta')|))
        ≤ 2 * A' + (2 / Real.pi) * (q : ℝ) * Real.log (4 * q)) :
    (∑ n ∈ Finset.Ioc ⌊x⌋ ⌊y⌋,
        min A (B / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta)|))
      ≤ ((⌊(y - x) / (q : ℝ)⌋ : ℝ) + 1)
          * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
  classical
  set f : ℤ → ℝ := fun n => min A (B / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta)|) with hfdef
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    exact le_min hA.le (by positivity)
  -- the number of blocks
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hK0 : (0 : ℤ) ≤ ⌊(y - x) / (q : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = ⌊(y - x) / (q : ℝ)⌋ + 1 := ⟨(⌊(y - x) / (q : ℝ)⌋ + 1).toNat,
    Int.toNat_of_nonneg (by linarith)⟩
  -- the blocks cover `(x, y]`
  have hcover : ⌊y⌋ ≤ ⌊x⌋ + (k : ℤ) * q := by
    have h1 : (y - x) / (q : ℝ) < (⌊(y - x) / (q : ℝ)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have hkR : ((k : ℤ) : ℝ) = (⌊(y - x) / (q : ℝ)⌋ : ℝ) + 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hk
    have h2 : y - x < ((k : ℤ) : ℝ) * (q : ℝ) := by
      rw [hkR]
      calc y - x = ((y - x) / (q : ℝ)) * (q : ℝ) := by field_simp
        _ < ((⌊(y - x) / (q : ℝ)⌋ : ℝ) + 1) * (q : ℝ) := by
            exact (mul_lt_mul_of_pos_right h1 hqR)
    have h3 : y ≤ x + ((k : ℤ) : ℝ) * (q : ℝ) := by linarith
    have h4 : ⌊y⌋ ≤ ⌊x + ((k : ℤ) : ℝ) * (q : ℝ)⌋ := Int.floor_le_floor h3
    have h5 : ⌊x + ((k : ℤ) : ℝ) * (q : ℝ)⌋ = ⌊x⌋ + (k : ℤ) * q := by
      have : ((((k : ℤ) * q : ℤ)) : ℝ) = ((k : ℤ) : ℝ) * (q : ℝ) := by push_cast; ring
      rw [← this, Int.floor_add_intCast]
    omega
  have hsub : Finset.Ioc ⌊x⌋ ⌊y⌋ ⊆ Finset.Ioc ⌊x⌋ (⌊x⌋ + (k : ℤ) * q) :=
    Finset.Ioc_subset_Ioc_right hcover
  have hmono : (∑ n ∈ Finset.Ioc ⌊x⌋ ⌊y⌋, f n)
      ≤ ∑ n ∈ Finset.Ioc ⌊x⌋ (⌊x⌋ + (k : ℤ) * q), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)
  -- the single-block bound, in the un-normalised form
  set C : ℝ := 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) with hCdef
  have hC : ∀ m : ℤ, (∑ n ∈ Finset.Ioc m (m + (q : ℤ)), f n) ≤ C := by
    intro m
    have hb := hblock (A / B) theta (div_pos hA hB) m
    have hscale : ∀ n : ℤ, f n
        = B * min (A / B) (1 / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta)|) := by
      intro n
      rw [hfdef]
      simp only
      rw [mul_min_of_nonneg _ _ hB.le]
      congr 1
      · field_simp
      · field_simp
    calc (∑ n ∈ Finset.Ioc m (m + (q : ℤ)), f n)
        = B * ∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
            min (A / B) (1 / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta)|) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => hscale n)
      _ ≤ B * (2 * (A / B) + (2 / Real.pi) * (q : ℝ) * Real.log (4 * q)) := by
          exact mul_le_mul_of_nonneg_left hb hB.le
      _ = C := by rw [hCdef]; field_simp
  have hmain := blocks_le q hq f hf C hC k ⌊x⌋
  have hkR : (k : ℝ) = (⌊(y - x) / (q : ℝ)⌋ : ℝ) + 1 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at this
    exact this
  rw [hkR] at hmain
  exact le_trans hmono hmain

end TaoVino
end PartVino

theorem solution (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (halpha : alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (theta x y : ℝ) (hxy : x < y)
    (hblock : ∀ (A' theta' : ℝ), 0 < A' → ∀ m : ℤ,
      (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
          min A' (1 / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta')|))
        ≤ 2 * A' + (2 / Real.pi) * (q : ℝ) * Real.log (4 * q)) :
    (∑ n ∈ Finset.Ioc ⌊x⌋ ⌊y⌋,
        min A (B / |Real.sin (Real.pi * (alpha * (n : ℝ)) + theta)|))
      ≤ ((⌊(y - x) / (q : ℝ)⌋ : ℝ) + 1)
          * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) :=
  TaoVino.vinogradov alpha beta a q hq halpha hbeta A B hA hB theta x y hxy hblock
