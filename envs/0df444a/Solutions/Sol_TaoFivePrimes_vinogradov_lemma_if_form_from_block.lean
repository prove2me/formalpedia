-- Prove2me | solution 1 for TaoFivePrimes.vinogradov_lemma_if_form_from_block
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:48:08.158003+00:00
-- url     : https://prove2.me/submissions/4d3ce059-94a2-4af9-92fc-2af9403c9a8e

import Mathlib

open Finset

section PartVS
open Finset

namespace TaoVS

theorem blocks_sum (L : ℤ) (hL : 0 < L) (f : ℤ → ℝ) (C : ℕ → ℝ) (m : ℤ)
    (hC : ∀ j : ℕ, (∑ n ∈ Finset.Ioc (m + (j : ℤ) * L) (m + ((j : ℤ) + 1) * L), f n) ≤ C j) :
    ∀ k : ℕ, (∑ n ∈ Finset.Ioc m (m + (k : ℤ) * L), f n) ≤ ∑ j ∈ Finset.range k, C j := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hle1 : m ≤ m + (k : ℤ) * L := by nlinarith [Int.natCast_nonneg k, hL.le]
      have hshape : m + ((k : ℕ) + 1 : ℤ) * L = (m + (k : ℤ) * L) + L := by ring
      have hle2 : m + (k : ℤ) * L ≤ (m + (k : ℤ) * L) + L := by linarith
      have hdisj : Disjoint (Finset.Ioc m (m + (k : ℤ) * L))
          (Finset.Ioc (m + (k : ℤ) * L) ((m + (k : ℤ) * L) + L)) := by
        rw [Finset.disjoint_left]
        intro n hn hn'
        rw [Finset.mem_Ioc] at hn hn'
        omega
      have hunion : Finset.Ioc m (m + (k : ℤ) * L)
          ∪ Finset.Ioc (m + (k : ℤ) * L) ((m + (k : ℤ) * L) + L)
          = Finset.Ioc m ((m + (k : ℤ) * L) + L) :=
        Finset.Ioc_union_Ioc_eq_Ioc hle1 hle2
      have hsplit : (∑ n ∈ Finset.Ioc m ((m + (k : ℤ) * L) + L), f n)
          = (∑ n ∈ Finset.Ioc m (m + (k : ℤ) * L), f n)
            + ∑ n ∈ Finset.Ioc (m + (k : ℤ) * L) ((m + (k : ℤ) * L) + L), f n := by
        rw [← hunion, Finset.sum_union hdisj]
      have h2 : (∑ n ∈ Finset.Ioc (m + (k : ℤ) * L) ((m + (k : ℤ) * L) + L), f n) ≤ C k := by
        have := hC k
        rw [show m + ((k : ℤ) + 1) * L = (m + (k : ℤ) * L) + L by ring] at this
        exact this
      have hcast : ((k + 1 : ℕ) : ℤ) * L = ((k : ℕ) + 1 : ℤ) * L := by push_cast; ring
      calc (∑ n ∈ Finset.Ioc m (m + ((k + 1 : ℕ) : ℤ) * L), f n)
          = ∑ n ∈ Finset.Ioc m ((m + (k : ℤ) * L) + L), f n := by rw [hcast, hshape]
        _ = (∑ n ∈ Finset.Ioc m (m + (k : ℤ) * L), f n)
              + ∑ n ∈ Finset.Ioc (m + (k : ℤ) * L) ((m + (k : ℤ) * L) + L), f n := hsplit
        _ ≤ (∑ j ∈ Finset.range k, C j) + C k := by linarith [ih, h2]
        _ = ∑ j ∈ Finset.range (k + 1), C j := (Finset.sum_range_succ C k).symm

theorem subdivision (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' theta' u v : ℝ) (hA' : 0 ≤ A') (huv : u < v)
    (hblock : ∀ m : ℤ,
      (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
          (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
            else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
        ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
  classical
  set f : ℤ → ℝ := fun n =>
    (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
      else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)) with hf
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n; rw [hf]; dsimp only; split_ifs
    · exact hA'
    · exact le_min hA' (by positivity)
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hpos : (0:ℝ) < (v - u) / (q:ℝ) := by positivity
  set N : ℤ := ⌊(v - u) / (q:ℝ)⌋ with hN
  have hN0 : 0 ≤ N := Int.floor_nonneg.mpr hpos.le
  set K : ℕ := N.toNat + 1 with hK
  have hKz : (K : ℤ) = N + 1 := by rw [hK]; push_cast; omega
  have hNgt : (v - u) / (q:ℝ) < (N : ℝ) + 1 := Int.lt_floor_add_one _
  have hcover : ⌊v⌋ ≤ ⌊u⌋ + (K : ℤ) * (q : ℤ) := by
    have h1 : v - u < ((N:ℝ) + 1) * (q:ℝ) := by
      rw [div_lt_iff₀ hqR] at hNgt; linarith
    have h2 : ((⌊v⌋ : ℤ) : ℝ) ≤ v := Int.floor_le v
    have h3 : u - 1 < ((⌊u⌋ : ℤ) : ℝ) := by
      have := Int.sub_one_lt_floor u; linarith
    have h4 : ((⌊v⌋ : ℤ) : ℝ) - ((⌊u⌋ : ℤ) : ℝ) < ((N:ℝ) + 1) * (q:ℝ) + 1 := by linarith
    have h5 : ((⌊v⌋ - ⌊u⌋ : ℤ) : ℝ) < (((N + 1) * (q:ℤ) : ℤ) : ℝ) + 1 := by
      push_cast; push_cast at h4; linarith
    have h6 : (⌊v⌋ - ⌊u⌋ : ℤ) < (N + 1) * (q:ℤ) + 1 := by exact_mod_cast h5
    rw [hKz]; omega
  have hsub : (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋, f n)
      ≤ ∑ n ∈ Finset.Ioc ⌊u⌋ (⌊u⌋ + (K : ℤ) * (q : ℤ)), f n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hf0 n)
    exact Finset.Ioc_subset_Ioc_right hcover
  have hC : ∀ j : ℕ, (∑ n ∈ Finset.Ioc (⌊u⌋ + (j : ℤ) * (q:ℤ)) (⌊u⌋ + ((j : ℤ) + 1) * (q:ℤ)), f n)
      ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
    intro j
    have := hblock (⌊u⌋ + (j : ℤ) * (q:ℤ))
    rw [show ⌊u⌋ + ((j : ℤ) + 1) * (q:ℤ) = (⌊u⌋ + (j : ℤ) * (q:ℤ)) + (q:ℤ) by ring]
    exact this
  have hmain := blocks_sum (q:ℤ) (by exact_mod_cast hq) f
    (fun _ => 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) ⌊u⌋ hC K
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hmain
  have hKR : ((K : ℕ) : ℝ) = ((N : ℤ) : ℝ) + 1 := by
    have : ((K : ℕ) : ℤ) = N + 1 := hKz
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  rw [hKR] at hmain
  linarith [hsub, hmain]

end TaoVS

end PartVS

theorem solution
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' theta' u v : ℝ) (hA' : 0 ≤ A') (huv : u < v)
    (hblock : ∀ m : ℤ,
      (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
          (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
            else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
        ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) :=
  TaoVS.subdivision B hB q hq A' alpha' theta' u v hA' huv hblock
