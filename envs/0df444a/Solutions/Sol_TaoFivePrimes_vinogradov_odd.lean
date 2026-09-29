-- Prove2me | solution 1 for TaoFivePrimes.vinogradov_odd
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T23:55:36.285185+00:00
-- url     : https://prove2.me/submissions/b0f3a676-99cb-419e-9d2b-567bee4d2851

import Mathlib

open Finset

namespace TaoV35

/-- Integers in `(x, y]` are exactly the integers in `Ioc ⌊x⌋ ⌊y⌋`. -/
theorem mem_Ioc_floor {x y : ℝ} (n : ℤ) : n ∈ Finset.Ioc ⌊x⌋ ⌊y⌋ ↔ (x < (n : ℝ) ∧ (n : ℝ) ≤ y) := by
  simp only [Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Int.floor_lt).mp h1, Int.le_floor.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Int.floor_lt.mpr h1, Int.le_floor.mpr h2⟩

/-- The odd integers of `(x,y]` are the image of the integers of `((x-1)/2, (y-1)/2]`
under `m ↦ 2m+1`. -/
theorem sum_odd_reindex {x y : ℝ} (f : ℤ → ℝ) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋ ⌊y⌋).filter (fun n : ℤ => Odd n), f n)
      = ∑ m ∈ Finset.Ioc ⌊(x - 1) / 2⌋ ⌊(y - 1) / 2⌋, f (2 * m + 1) := by
  classical
  refine (Finset.sum_nbij' (i := fun m => 2 * m + 1) (j := fun n => (n - 1) / 2)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro m hm
    rw [mem_Ioc_floor] at hm
    simp only [Finset.mem_filter]
    refine ⟨(mem_Ioc_floor _).mpr ⟨?_, ?_⟩, ⟨m, by ring⟩⟩
    · push_cast
      linarith [hm.1]
    · push_cast
      linarith [hm.2]
  · intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨hmem, k, hk⟩ := hn
    rw [mem_Ioc_floor] at hmem
    rw [mem_Ioc_floor]
    have hnk : n = 2 * k + 1 := by omega
    have hdiv : (n - 1) / 2 = k := by omega
    rw [hdiv]
    subst hnk
    push_cast at hmem ⊢
    constructor
    · linarith [hmem.1]
    · linarith [hmem.2]
  · intro m _
    omega
  · intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨_, k, hk⟩ := hn
    omega
  · intro m _
    rfl

/-- Tao's summand `min(A, B/|sin θ|)`, with his convention `B/0 = +∞` (so the term is `A`
when the sine vanishes).  Lean's `B/0 = 0` would silently weaken the statement. -/
noncomputable def vterm (A B s : ℝ) : ℝ := if s = 0 then A else min A (B / |s|)

/-- **Tao, Corollary 3.5 (restriction to odd integers)**, deduced from Lemma 3.4. -/
theorem vino_odd (A B : ℝ) {alpha beta theta : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (halpha : 2 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    {x y : ℝ} (hxy : x < y)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            vterm A B (Real.sin (Real.pi * alpha' * (n : ℝ) + theta')))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋ ⌊y⌋).filter (fun n : ℤ => Odd n),
        vterm A B (Real.sin (Real.pi * alpha * (n : ℝ) + theta)))
      ≤ ((⌊(y - x) / (2 * (q : ℝ))⌋ : ℤ) + 1)
          * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
  classical
  rw [sum_odd_reindex
    (fun n : ℤ => vterm A B (Real.sin (Real.pi * alpha * (n : ℝ) + theta)))]
  have hsin : ∀ m : ℤ, Real.pi * alpha * (((2 * m + 1 : ℤ)) : ℝ) + theta
      = Real.pi * (2 * alpha) * (m : ℝ) + (Real.pi * alpha + theta) := by
    intro m; push_cast; ring
  simp only [hsin]
  have huv : (x - 1) / 2 < (y - 1) / 2 := by linarith
  have h := hvino (2 * alpha) beta (Real.pi * alpha + theta) ((x - 1) / 2) ((y - 1) / 2) a
    halpha hbeta huv
  have hlen : ((y - 1) / 2 - (x - 1) / 2) / (q : ℝ) = (y - x) / (2 * (q : ℝ)) := by
    field_simp
    ring
  rw [hlen] at h
  exact h




end TaoV35

theorem solution
    (A B : ℝ) (alpha beta theta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (halpha : 2 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x y : ℝ) (hxy : x < y)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A
              else min A (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋ ⌊y⌋).filter (fun n : ℤ => Odd n),
        (if Real.sin (Real.pi * alpha * (n : ℝ) + theta) = 0 then A
          else min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|)))
      ≤ ((⌊(y - x) / (2 * (q : ℝ))⌋ : ℤ) + 1)
          * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) :=
  TaoV35.vino_odd A B hq halpha hbeta hxy hvino
