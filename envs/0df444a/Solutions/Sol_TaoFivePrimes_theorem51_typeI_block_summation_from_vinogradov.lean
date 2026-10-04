-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeI_block_summation_from_vinogradov
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:40:20.558139+00:00
-- url     : https://prove2.me/submissions/e367376e-c1a3-4bfb-8525-725c94de5560

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_typeI_small_divisor_contribution
import Theorems.Thm_TaoFivePrimes_vinogradov_odd
import Theorems.Thm_TaoFivePrimes_typeI_block_sum_bound
import Theorems.Thm_TaoFivePrimes_sin_lower_bound_small_divisor

open Finset

section PartTI
open Finset

namespace TaoS5T

/-- The Type I weight with truncation level `A`, using the source's convention at the
zeros of the sine. -/
noncomputable def wgt (A B alpha : ℝ) (d : ℤ) : ℝ :=
  if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then A
    else min A (B / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)

theorem wgt_mono {A A' B alpha : ℝ} (h : A ≤ A') (d : ℤ) :
    wgt A B alpha d ≤ wgt A' B alpha d := by
  unfold wgt
  split_ifs with hs
  · exact h
  · exact min_le_min h le_rfl

/-- Summing a function over `k` consecutive blocks of length `L`. -/
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

/-- Lemma 3.4 for the fixed second parameter `B` and every truncation level, in the shape
that Corollary 3.5 consumes. -/
def VinoHyp (B : ℝ) (q : ℕ) : Prop :=
  ∀ (A' alpha' beta' theta' u v : ℝ) (a' : ℤ), 0 ≤ A' →
    alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))

/-- One block of length `2q`: Corollary 3.5 with block count `2`. -/
theorem block_bound (A B alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q) (hA : 0 ≤ A)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hvino : VinoHyp B q) (m : ℤ) :
    (∑ d ∈ (Finset.Ioc m (m + 2 * (q : ℤ))).filter (fun d : ℤ => Odd d), wgt A B alpha d)
      ≤ 2 * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  set u : ℝ := (m : ℝ) with hu
  set v : ℝ := (m : ℝ) + 2 * (q : ℝ) with hv
  have huv : u < v := by rw [hu, hv]; linarith
  have hcor := TaoFivePrimes.vinogradov_odd A B (2 * alpha) beta 0 a q hq
    (by rw [← halpha]; ring) hbeta u v huv (fun a1 a2 a3 a4 a5 a6 h1 h2 h3 => hvino A a1 a2 a3 a4 a5 a6 hA h1 h2 h3)
  have hfu : ⌊u⌋ = m := by rw [hu]; exact Int.floor_intCast m
  have hfv : ⌊v⌋ = m + 2 * (q : ℤ) := by
    rw [hv, show (m : ℝ) + 2 * (q : ℝ) = ((m + 2 * (q : ℤ) : ℤ) : ℝ) by push_cast; ring]
    exact Int.floor_intCast _
  have hfloor : (⌊(v - u) / (2 * (q : ℝ))⌋ : ℤ) = 1 := by
    have h1 : v - u = 2 * (q : ℝ) := by rw [hu, hv]; ring
    rw [h1, div_self (by positivity)]
    exact Int.floor_one
  rw [hfu, hfv, hfloor] at hcor
  simp only [Int.cast_one, add_zero] at hcor
  have hnum : ((1 : ℤ) : ℝ) + 1 = 2 := by norm_num
  calc (∑ d ∈ (Finset.Ioc m (m + 2 * (q : ℤ))).filter (fun d : ℤ => Odd d), wgt A B alpha d)
      = ∑ d ∈ (Finset.Ioc m (m + 2 * (q : ℤ))).filter (fun d : ℤ => Odd d),
          (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then A
            else min A (B / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)) := rfl
    _ ≤ 2 * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
        have h2 : ((1:ℝ) + 1) = 2 := by norm_num
        rw [h2] at hcor
        exact hcor

theorem wgt_nonneg {A B alpha : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (d : ℤ) : 0 ≤ wgt A B alpha d := by
  unfold wgt
  split_ifs with h
  · exact hA
  · exact le_min hA (by positivity)

/-- **Tao, Section 5, the Type I estimate** (with corrected constants; see the Deviation
note on the statement). -/
theorem typeI_total
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x M Lx Cb : ℝ) (hx : 0 < x) (hLx : 0 ≤ Lx) (hCb : 0 ≤ Cb) (hM : (q : ℝ) / 2 ≤ M)
    (hvino : VinoHyp Cb q)
    (W : ℤ → ℝ) (hW0 : ∀ d, 0 ≤ W d)
    (hWb : ∀ d : ℤ, 1 ≤ d → (d : ℝ) ≤ M →
        W d ≤ wgt ((1 / 2) * (x / (d : ℝ)) * Lx + Cb) Cb alpha d) :
    (∑ d ∈ (Finset.Ioc (0 : ℤ) ⌊M⌋).filter (fun d : ℤ => Odd d), W d)
      ≤ (2 * (q : ℝ) * Cb + (1 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q))
        + ((x / q) * Lx * (Real.log (2 * M / q + 4) + 4)
           + ((⌊M / (2 * (q : ℝ)) - 1 / 4⌋₊ : ℝ) + 1)
               * (4 * Cb + (4 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q))) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set m0 : ℤ := ⌊(q : ℝ) / 2⌋ with hm0
  have hm0le : ((m0 : ℤ) : ℝ) ≤ (q : ℝ) / 2 := Int.floor_le _
  have hm0gt : (q : ℝ) / 2 - 1 < ((m0 : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have hm0pos : (1 : ℤ) ≤ m0 := by
    have : (1 : ℝ) ≤ (q : ℝ) / 2 := by linarith
    exact Int.le_floor.mpr (by exact_mod_cast this)
  set J : ℕ := ⌊M / (2 * (q : ℝ)) - 1 / 4⌋₊ with hJ
  set K : ℕ := J + 1 with hK
  have hMq : (0 : ℝ) ≤ M / (2 * (q : ℝ)) - 1 / 4 := by
    rw [le_sub_iff_add_le, zero_add, le_div_iff₀ (by positivity)]
    linarith
  have hJle : (J : ℝ) ≤ M / (2 * (q : ℝ)) - 1 / 4 := Nat.floor_le hMq
  have hKgt : M / (2 * (q : ℝ)) - 1 / 4 < (K : ℝ) := by
    rw [hK]
    push_cast
    exact Nat.lt_floor_add_one _
  -- the blocks cover the range
  have hcover : ⌊M⌋ ≤ m0 + (K : ℤ) * (2 * (q : ℤ)) := by
    have h1 : (M : ℝ) - 1 < ((m0 : ℤ) : ℝ) + (K : ℝ) * (2 * (q : ℝ)) := by
      have h2 : M / (2 * (q : ℝ)) * (2 * (q : ℝ)) = M := by field_simp
      have h3 : (M / (2 * (q : ℝ)) - 1 / 4) * (2 * (q : ℝ)) < (K : ℝ) * (2 * (q : ℝ)) :=
        mul_lt_mul_of_pos_right hKgt (by positivity)
      nlinarith [h2, h3, hm0gt]
    have h4 : ((⌊M⌋ : ℤ) : ℝ) ≤ M := Int.floor_le M
    have h5 : ((m0 + (K : ℤ) * (2 * (q : ℤ)) : ℤ) : ℝ)
        = ((m0 : ℤ) : ℝ) + (K : ℝ) * (2 * (q : ℝ)) := by push_cast; ring
    have h6 : ((⌊M⌋ : ℤ) : ℝ) - 1 < ((m0 + (K : ℤ) * (2 * (q : ℤ)) : ℤ) : ℝ) := by
      rw [h5]; linarith
    have h7 : (⌊M⌋ : ℤ) - 1 < m0 + (K : ℤ) * (2 * (q : ℤ)) := by exact_mod_cast h6
    omega
  have hm0M : m0 ≤ ⌊M⌋ := by
    have : ((m0 : ℤ) : ℝ) ≤ M := le_trans hm0le hM
    exact Int.le_floor.mpr this
  -- split off the small divisors
  set P : Finset ℤ := (Finset.Ioc (0 : ℤ) ⌊M⌋).filter (fun d : ℤ => Odd d) with hP
  set P1 : Finset ℤ := (Finset.Ioc (0 : ℤ) m0).filter (fun d : ℤ => Odd d) with hP1
  set P2 : Finset ℤ := (Finset.Ioc m0 ⌊M⌋).filter (fun d : ℤ => Odd d) with hP2
  have hPsplit : (∑ d ∈ P, W d) = (∑ d ∈ P1, W d) + ∑ d ∈ P2, W d := by
    rw [hP, hP1, hP2, ← Finset.sum_filter_add_sum_filter_not
      ((Finset.Ioc (0 : ℤ) ⌊M⌋).filter (fun d : ℤ => Odd d)) (fun d => d ≤ m0)]
    congr 1
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, le_trans h2 hm0M⟩, h3⟩, h2⟩
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc, not_le]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h4, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨by omega, h2⟩, h3⟩, h1⟩
  -- the small divisors
  have hpart1 : (∑ d ∈ P1, W d)
      ≤ 2 * (q : ℝ) * Cb + (1 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q) := by
    have hbnd : ∀ d ∈ P1, W d ≤ wgt (2 * (q : ℝ) * Cb) Cb alpha d := by
      intro d hd
      rw [hP1, Finset.mem_filter, Finset.mem_Ioc] at hd
      obtain ⟨⟨hd1, hd2⟩, hdodd⟩ := hd
      have hdR : ((d : ℤ) : ℝ) ≤ (q : ℝ) / 2 := by
        have : ((d : ℤ) : ℝ) ≤ ((m0 : ℤ) : ℝ) := by exact_mod_cast hd2
        linarith
      have hdM : ((d : ℤ) : ℝ) ≤ M := le_trans hdR hM
      have hdnat : 2 * d.toNat ≤ q := by
        have h1 : ((d.toNat : ℤ) : ℝ) = ((d : ℤ) : ℝ) := by
          rw [Int.toNat_of_nonneg (by omega)]
        have h2 : (2 : ℝ) * ((d.toNat : ℕ) : ℝ) ≤ (q : ℝ) := by
          push_cast at h1 ⊢
          linarith
        exact_mod_cast h2
      have hsep := (TaoFivePrimes.sin_lower_bound_small_divisor alpha beta a q hq haq halpha
        hbeta d.toNat (by omega) hdnat).2
      have hcast : ((d.toNat : ℕ) : ℝ) = ((d : ℤ) : ℝ) := by
        have hz : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
      rw [hcast] at hsep
      have hform : 2 * Real.pi * ((d : ℤ) : ℝ) * alpha
          = Real.pi * (2 * alpha) * ((d : ℤ) : ℝ) := by ring
      rw [hform] at hsep
      have hpos : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      have hsin : Real.sin (Real.pi * (2 * alpha) * ((d : ℤ) : ℝ)) ≠ 0 := by
        intro hz
        rw [hz, abs_zero] at hsep
        linarith
      have hW := hWb d hd1 hdM
      unfold wgt at hW ⊢
      rw [if_neg hsin] at hW ⊢
      have habs : (0 : ℝ) < |Real.sin (Real.pi * (2 * alpha) * ((d : ℤ) : ℝ))| := abs_pos.mpr hsin
      have hquot : Cb / |Real.sin (Real.pi * (2 * alpha) * ((d : ℤ) : ℝ))| ≤ 2 * (q : ℝ) * Cb := by
        rw [div_le_iff₀ habs]
        have h1 : 2 * (q : ℝ) * Cb * (1 / (2 * (q : ℝ))) = Cb := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hsep
          (show (0:ℝ) ≤ 2 * (q : ℝ) * Cb by positivity), h1]
      refine le_trans hW ?_
      refine le_min ?_ (min_le_right _ _)
      exact le_trans (min_le_right _ _) hquot
    have hsum : (∑ d ∈ P1, W d) ≤ ∑ d ∈ P1, wgt (2 * (q : ℝ) * Cb) Cb alpha d :=
      Finset.sum_le_sum hbnd
    have himp := TaoFivePrimes.typeI_small_divisor_contribution (2 * (q : ℝ) * Cb) Cb alpha beta
      a q hq (by positivity) hCb halpha hbeta (fun a1 a2 a3 a4 a5 a6 h1 h2 h3 => hvino (2 * (q : ℝ) * Cb) a1 a2 a3 a4 a5 a6 (by positivity) h1 h2 h3)
    exact le_trans hsum himp
  -- the blocks
  have hpart2 : (∑ d ∈ P2, W d)
      ≤ (x / q) * Lx * (Real.log (2 * M / q + 4) + 4)
        + (K : ℝ) * (4 * Cb + (4 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q)) := by
    set V : ℤ → ℝ := fun d => if d ≤ ⌊M⌋ then W d else 0 with hV
    set f : ℤ → ℝ := fun d => if Odd d then V d else 0 with hf
    have hf0 : ∀ d, 0 ≤ f d := by
      intro d
      rw [hf, hV]
      dsimp only
      split_ifs
      · exact hW0 d
      · exact le_rfl
      · exact le_rfl
    have hstep1 : (∑ d ∈ P2, W d) = ∑ d ∈ Finset.Ioc m0 ⌊M⌋, f d := by
      rw [hP2, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      rw [Finset.mem_Ioc] at hd
      rw [hf, hV]
      dsimp only
      rw [if_pos hd.2]
    have hstep2 : (∑ d ∈ Finset.Ioc m0 ⌊M⌋, f d)
        ≤ ∑ d ∈ Finset.Ioc m0 (m0 + (K : ℤ) * (2 * (q : ℤ))), f d := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hf0 d)
      exact Finset.Ioc_subset_Ioc_right hcover
    set Aj : ℕ → ℝ := fun j => (1 / 2) * (x / ((q : ℝ) / 2 + 2 * (j : ℝ) * (q : ℝ))) * Lx + Cb
      with hAj
    set C : ℕ → ℝ := fun j =>
      2 * (2 * Aj j + (2 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q)) with hC
    have hAj0 : ∀ j, 0 ≤ Aj j := by
      intro j
      rw [hAj]
      dsimp only
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hden : (0 : ℝ) < (q : ℝ) / 2 + 2 * (j : ℝ) * (q : ℝ) := by positivity
      positivity
    have hCbnd : ∀ j : ℕ,
        (∑ n ∈ Finset.Ioc (m0 + (j : ℤ) * (2 * (q : ℤ))) (m0 + ((j : ℤ) + 1) * (2 * (q : ℤ))), f n)
          ≤ C j := by
      intro j
      have hmap : (∑ n ∈ Finset.Ioc (m0 + (j : ℤ) * (2 * (q : ℤ)))
            (m0 + ((j : ℤ) + 1) * (2 * (q : ℤ))), f n)
          = ∑ n ∈ (Finset.Ioc (m0 + (j : ℤ) * (2 * (q : ℤ)))
              ((m0 + (j : ℤ) * (2 * (q : ℤ))) + 2 * (q : ℤ))).filter (fun n : ℤ => Odd n), V n := by
        rw [Finset.sum_filter, show m0 + ((j : ℤ) + 1) * (2 * (q : ℤ))
          = (m0 + (j : ℤ) * (2 * (q : ℤ))) + 2 * (q : ℤ) by ring]
      rw [hmap]
      have hle : ∀ n ∈ (Finset.Ioc (m0 + (j : ℤ) * (2 * (q : ℤ)))
            ((m0 + (j : ℤ) * (2 * (q : ℤ))) + 2 * (q : ℤ))).filter (fun n : ℤ => Odd n),
          V n ≤ wgt (Aj j) Cb alpha n := by
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Ioc] at hn
        obtain ⟨⟨hn1, hn2⟩, hnodd⟩ := hn
        have hnlow : (q : ℝ) / 2 + 2 * (j : ℝ) * (q : ℝ) ≤ ((n : ℤ) : ℝ) := by
          have h1 : m0 + (j : ℤ) * (2 * (q : ℤ)) + 1 ≤ n := by omega
          have h2 : ((m0 : ℤ) : ℝ) + (j : ℝ) * (2 * (q : ℝ)) + 1 ≤ ((n : ℤ) : ℝ) := by
            have := (Int.cast_le (R := ℝ)).mpr h1
            push_cast at this
            linarith
          linarith [hm0gt]
        have hn1' : (1 : ℤ) ≤ n := by
          have hj0 : (0 : ℤ) ≤ (j : ℤ) * (2 * (q : ℤ)) := by positivity
          omega
        rw [hV]
        dsimp only
        by_cases hnM : n ≤ ⌊M⌋
        · rw [if_pos hnM]
          have hnMR : ((n : ℤ) : ℝ) ≤ M := le_trans (by exact_mod_cast hnM) (Int.floor_le M)
          refine le_trans (hWb n hn1' hnMR) (wgt_mono ?_ n)
          have hnpos : (0 : ℝ) < ((n : ℤ) : ℝ) := by
            have : (1 : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hn1'
            linarith
          have hden : (0 : ℝ) < (q : ℝ) / 2 + 2 * (j : ℝ) * (q : ℝ) := by
            have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
            positivity
          have hdiv : x / ((n : ℤ) : ℝ) ≤ x / ((q : ℝ) / 2 + 2 * (j : ℝ) * (q : ℝ)) :=
            div_le_div_of_nonneg_left hx.le hden hnlow
          rw [hAj]
          dsimp only
          nlinarith [hdiv, hLx]
        · rw [if_neg hnM]
          exact wgt_nonneg (hAj0 j) hCb n
      refine le_trans (Finset.sum_le_sum hle) ?_
      exact block_bound (Aj j) Cb alpha beta a q (by omega) (hAj0 j) halpha hbeta hvino _
    have hblocks := blocks_sum (2 * (q : ℤ)) (by positivity) f C m0 hCbnd K
    -- evaluate the sum of the block bounds
    have hCsum : (∑ j ∈ Finset.range K, C j)
        = 2 * Lx * (∑ j ∈ Finset.range K, x / (2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2))
          + (K : ℝ) * (4 * Cb + (4 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q)) := by
      have hpt : ∀ j ∈ Finset.range K, C j
          = 2 * Lx * (x / (2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2))
            + (4 * Cb + (4 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q)) := by
        intro j _
        simp only [hC, hAj]
        have hcomm : (q : ℝ) / 2 + 2 * (j : ℝ) * (q : ℝ)
            = 2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2 := by ring
        rw [hcomm]
        ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have himp := TaoFivePrimes.typeI_block_sum_bound x (q : ℝ) M hx.le hqR J hJle
    have hKJ : K = J + 1 := hK
    rw [← hKJ] at himp
    have hLx2 : (0 : ℝ) ≤ 2 * Lx := by linarith
    have hfin : 2 * Lx * (∑ j ∈ Finset.range K, x / (2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2))
        ≤ (x / q) * Lx * (Real.log (2 * M / q + 4) + 4) := by
      have := mul_le_mul_of_nonneg_left himp hLx2
      have heq : 2 * Lx * ((x / (2 * (q : ℝ))) * (Real.log (2 * M / (q : ℝ) + 4) + 4))
          = (x / q) * Lx * (Real.log (2 * M / q + 4) + 4) := by
        field_simp
      linarith [this, heq]
    rw [hstep1]
    calc (∑ d ∈ Finset.Ioc m0 ⌊M⌋, f d)
        ≤ ∑ d ∈ Finset.Ioc m0 (m0 + (K : ℤ) * (2 * (q : ℤ))), f d := hstep2
      _ ≤ ∑ j ∈ Finset.range K, C j := hblocks
      _ = 2 * Lx * (∑ j ∈ Finset.range K, x / (2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2))
            + (K : ℝ) * (4 * Cb + (4 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q)) := hCsum
      _ ≤ (x / q) * Lx * (Real.log (2 * M / q + 4) + 4)
            + (K : ℝ) * (4 * Cb + (4 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q)) := by
          linarith [hfin]
  have hKcast : ((⌊M / (2 * (q : ℝ)) - 1 / 4⌋₊ : ℝ) + 1) = (K : ℝ) := by
    rw [hK, hJ]; push_cast; ring
  rw [hPsplit, hKcast]
  linarith [hpart1, hpart2]

end TaoS5T

namespace TaoTIB

theorem sum_divisors_eq (U V : ℝ) (hM : 0 ≤ U * V) (W : ℕ → ℝ) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d)
      = ∑ n ∈ (Finset.Ioc (0:ℤ) ⌊U * V⌋).filter (fun n : ℤ => Odd n), W n.toNat := by
  classical
  have hfl : ((⌊U * V⌋₊ : ℕ) : ℤ) = ⌊U * V⌋ := Int.natCast_floor_eq_floor hM
  refine Finset.sum_nbij' (i := fun d : ℕ => (d : ℤ)) (j := fun n : ℤ => n.toNat) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [TaoFivePrimes.theorem51Divisors, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hd
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by exact_mod_cast h1, ?_⟩, ?_⟩
    · rw [← hfl]; exact_mod_cast h2
    · have : Odd d := Nat.coprime_two_right.mp h3
      exact_mod_cast this
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    simp only [TaoFivePrimes.theorem51Divisors, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have : n ≤ ((⌊U * V⌋₊ : ℕ) : ℤ) := by rw [hfl]; exact h2
      omega
    · refine Nat.coprime_two_right.mpr ?_
      have hz : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
      have : Odd ((n.toNat : ℕ) : ℤ) := by rw [hz]; exact h3
      exact_mod_cast this
  · intro d _; simp
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    exact Int.toNat_of_nonneg (by omega)
  · intro d _; simp

end TaoTIB

namespace TaoTIB

/-- The numerical step: the small-divisor and block-bookkeeping terms of the Type I
estimate fit inside `1.78 (UV + 5q/2)(8 + log q) log 2x`. -/
theorem numeric (q M L T Cb K p G : ℝ)
    (hq : 4 ≤ q) (hM : 0 ≤ M) (hL : 1.386 ≤ L) (hT : 0 ≤ T)
    (hCb0 : 0 ≤ Cb) (hCb : Cb ≤ 2.7728 * T)
    (hK : K ≤ M / (2 * q) + 3 / 4) (hK0 : 0 ≤ K)
    (hp0 : 0 ≤ p) (hp : p ≤ 0.3184) (hG0 : 0 ≤ G) (hG : G ≤ 1.3864 + L) :
    2 * q * Cb + p * Cb * q * G + K * (4 * Cb + 4 * p * Cb * q * G)
      ≤ 1.78 * (M + (5 / 2) * q) * (8 + L) * T := by
  have hq0 : (0:ℝ) < q := by linarith
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hZ0 : (0:ℝ) ≤ p * q * G := by positivity
  have h4K : 4 * K ≤ M / 2 + 3 := by
    have hd : M / (2 * q) ≤ M / 8 :=
      div_le_div_of_nonneg_left hM (by norm_num) (by linarith)
    linarith
  have hKZ : K * (p * q * G) ≤ (M / (2 * q) + 3 / 4) * (p * q * G) :=
    mul_le_mul_of_nonneg_right hK hZ0
  have hKZ2 : (M / (2 * q) + 3 / 4) * (p * q * G) = (1/2) * (p * G * M) + (3/4) * (p * q * G) := by
    field_simp
  have h4KZ : 4 * (K * (p * q * G)) ≤ 2 * (p * G * M) + 3 * (p * q * G) := by
    rw [hKZ2] at hKZ; linarith
  have a1 : p * (q * G) ≤ 0.3184 * (q * G) :=
    mul_le_mul_of_nonneg_right hp (mul_nonneg hq0.le hG0)
  have a2 : q * G ≤ q * (1.3864 + L) := mul_le_mul_of_nonneg_left hG hq0.le
  have hpqG : p * q * G ≤ 0.44143 * q + 0.3184 * (q * L) := by nlinarith [a1, a2]
  have b1 : p * (G * M) ≤ 0.3184 * (G * M) :=
    mul_le_mul_of_nonneg_right hp (mul_nonneg hG0 hM)
  have b2 : G * M ≤ (1.3864 + L) * M := mul_le_mul_of_nonneg_right hG hM
  have hpGM : p * G * M ≤ 0.44143 * M + 0.3184 * (M * L) := by nlinarith [b1, b2]
  have hbr : 2 * q + p * q * G + K * (4 + 4 * (p * q * G))
      ≤ 3.76572 * q + 3 + 1.2736 * (q * L) + 1.38287 * M + 0.6368 * (M * L) := by
    have hexp : K * (4 + 4 * (p * q * G)) = 4 * K + 4 * (K * (p * q * G)) := by ring
    rw [hexp]
    linarith [h4K, h4KZ, hpqG, hpGM]
  have hbr0 : (0:ℝ) ≤ 2 * q + p * q * G + K * (4 + 4 * (p * q * G)) := by positivity
  have hstep : 2 * q * Cb + p * Cb * q * G + K * (4 * Cb + 4 * p * Cb * q * G)
      = Cb * (2 * q + p * q * G + K * (4 + 4 * (p * q * G))) := by ring
  have hmul : Cb * (2 * q + p * q * G + K * (4 + 4 * (p * q * G)))
      ≤ (2.7728 * T) * (3.76572 * q + 3 + 1.2736 * (q * L) + 1.38287 * M + 0.6368 * (M * L)) :=
    mul_le_mul hCb hbr hbr0 (by positivity)
  have hcore : (8.3184 : ℝ)
      ≤ 25.158 * q + 0.91844 * (q * L) + 10.4055 * M + 0.01427 * (M * L) := by
    nlinarith [mul_nonneg hq0.le hL0, mul_nonneg hM hL0]
  have hfin : (2.7728 * T) * (3.76572 * q + 3 + 1.2736 * (q * L) + 1.38287 * M + 0.6368 * (M * L))
      ≤ 1.78 * (M + (5 / 2) * q) * (8 + L) * T := by
    nlinarith [mul_le_mul_of_nonneg_left hcore hT]
  linarith [hstep, hmul, hfin]

end TaoTIB

namespace TaoTIB
open Finset

set_option maxHeartbeats 2000000 in
theorem block_summation
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUV : U * V ≤ x / 4)
    (hvino : ∀ (A' alpha' beta' theta' u v : ℝ) (a' : ℤ), 0 ≤ A' →
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
              else min A' (4 * Real.log 2 * Real.log (2 * x)
                / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A' + (2 / Real.pi) * (4 * Real.log 2 * Real.log (2 * x)) * (q : ℝ)
                  * Real.log (4 * q)))
    (W : ℕ → ℝ) (hW0 : ∀ d, 0 ≤ W d)
    (hWb : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V,
        W d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                  (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
                else min ((1 / 2) * (x / (d : ℝ)) * Real.log x
                    + 4 * Real.log 2 * Real.log (2 * x))
                  (4 * Real.log 2 * Real.log (2 * x)
                    / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d)
      ≤ (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by
  classical
  have hM1600 : (1600:ℝ) ≤ U * V := by nlinarith
  have hM0 : (0:ℝ) ≤ U * V := by linarith
  have hx6400 : (6400:ℝ) ≤ x := by linarith
  have hqR : (4:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hT0 : (0:ℝ) ≤ Real.log (2*x) := Real.log_nonneg (by linarith)
  have hLx0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hl2u : Real.log 2 ≤ 0.6932 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have hl2l : (0.6931:ℝ) ≤ Real.log 2 := le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
  set Cb : ℝ := 4 * Real.log 2 * Real.log (2 * x) with hCbdef
  have hCb0 : (0:ℝ) ≤ Cb := by rw [hCbdef]; positivity
  have hCbub : Cb ≤ 2.7728 * Real.log (2*x) := by
    rw [hCbdef]; nlinarith
  have hpi : (3.1415:ℝ) < Real.pi := by
    have := Real.pi_gt_d4; linarith
  have hpub : 1 / Real.pi ≤ 0.3184 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hp0 : (0:ℝ) ≤ 1 / Real.pi := by positivity
  have hLq : (1.386:ℝ) ≤ Real.log (q:ℝ) := by
    have h4 : Real.log 4 ≤ Real.log (q:ℝ) := Real.log_le_log (by norm_num) hqR
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    rw [this] at h4; linarith
  have hGub : Real.log (4 * (q:ℝ)) ≤ 1.3864 + Real.log (q:ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    rw [this]; linarith
  have hG0 : (0:ℝ) ≤ Real.log (4 * (q:ℝ)) := Real.log_nonneg (by linarith)
  -- the transported weight
  set W' : ℤ → ℝ := fun n => if 0 < n ∧ Odd n ∧ n ≤ ⌊U * V⌋ then W n.toNat else 0 with hW'def
  have hW'0 : ∀ n, 0 ≤ W' n := by
    intro n; rw [hW'def]; dsimp only; split_ifs
    · exact hW0 _
    · exact le_rfl
  have hfl : ((⌊U * V⌋₊ : ℕ) : ℤ) = ⌊U * V⌋ := Int.natCast_floor_eq_floor hM0
  have htrans : (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d)
      = ∑ n ∈ (Finset.Ioc (0:ℤ) ⌊U * V⌋).filter (fun n : ℤ => Odd n), W' n := by
    rw [sum_divisors_eq U V hM0 W]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [hW'def]; dsimp only
    rw [if_pos ⟨hn.1.1, hn.2, hn.1.2⟩]
  have hW'b : ∀ d : ℤ, 1 ≤ d → (d : ℝ) ≤ U * V →
      W' d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                (1 / 2) * (x / (d : ℝ)) * Real.log x + Cb
              else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + Cb)
                (Cb / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)) := by
    intro d hd1 hd2
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have hAnn : (0:ℝ) ≤ (1 / 2) * (x / (d : ℝ)) * Real.log x + Cb := by positivity
    have hrhs0 : (0:ℝ) ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                (1 / 2) * (x / (d : ℝ)) * Real.log x + Cb
              else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + Cb)
                (Cb / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)) := by
      split_ifs
      · exact hAnn
      · exact le_min hAnn (by positivity)
    rw [hW'def]; dsimp only
    by_cases hcond : 0 < d ∧ Odd d ∧ d ≤ ⌊U * V⌋
    · rw [if_pos hcond]
      obtain ⟨hpos, hodd, hle⟩ := hcond
      have hmem : d.toNat ∈ TaoFivePrimes.theorem51Divisors U V := by
        simp only [TaoFivePrimes.theorem51Divisors, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, ?_⟩, ?_⟩
        · have : d ≤ ((⌊U * V⌋₊ : ℕ) : ℤ) := by rw [hfl]; exact hle
          omega
        · refine Nat.coprime_two_right.mpr ?_
          have hz : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
          have : Odd ((d.toNat : ℕ) : ℤ) := by rw [hz]; exact hodd
          exact_mod_cast this
      have hcast : ((d.toNat : ℕ) : ℝ) = ((d : ℤ) : ℝ) := by
        have hz : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
      have := hWb d.toNat hmem
      rw [hcast] at this
      exact this
    · rw [if_neg hcond]
      exact hrhs0
  rw [htrans]
  have hfirst0 : (0:ℝ) ≤ (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4) := by
    have h0 : (0:ℝ) ≤ 2 * U * V / (q:ℝ) := by positivity
    have : (0:ℝ) ≤ Real.log (2 * U * V / q + 4) := Real.log_nonneg (by linarith)
    positivity
  by_cases hcase : (q:ℝ) / 2 ≤ U * V
  · have hmain := TaoS5T.typeI_total alpha beta a q (by omega) haq halpha hbeta
      x (U * V) (Real.log x) Cb hx hLx0 hCb0 hcase hvino W' hW'0 hW'b
    have hKub : ((⌊U * V / (2 * (q:ℝ)) - 1/4⌋₊ : ℝ) + 1) ≤ U * V / (2 * (q:ℝ)) + 3/4 := by
      have h := Nat.floor_le (show (0:ℝ) ≤ U * V / (2 * (q:ℝ)) - 1/4 by
        rw [le_sub_iff_add_le, zero_add, le_div_iff₀ (by positivity)]; linarith)
      linarith
    have hK0 : (0:ℝ) ≤ ((⌊U * V / (2 * (q:ℝ)) - 1/4⌋₊ : ℝ) + 1) := by positivity
    have hnum := numeric (q:ℝ) (U * V) (Real.log (q:ℝ)) (Real.log (2*x)) Cb
      ((⌊U * V / (2 * (q:ℝ)) - 1/4⌋₊ : ℝ) + 1) (1 / Real.pi) (Real.log (4 * (q:ℝ)))
      hqR hM0 hLq hT0 hCb0 hCbub hKub hK0 hp0 hpub hG0 hGub
    have hlogeq : Real.log (2 * (U * V) / (q:ℝ) + 4) = Real.log (2 * U * V / (q:ℝ) + 4) := by
      congr 1; ring
    rw [hlogeq, show (4:ℝ) / Real.pi = 4 * (1 / Real.pi) from by ring] at hmain
    linarith [hmain, hnum]
  · push_neg at hcase
    have hsub : (Finset.Ioc (0:ℤ) ⌊U * V⌋).filter (fun n : ℤ => Odd n)
        ⊆ (Finset.Ioc (0:ℤ) ⌊(q:ℝ)/2⌋).filter (fun d : ℤ => Odd d) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
      refine ⟨⟨hn.1.1, ?_⟩, hn.2⟩
      have : (⌊U * V⌋ : ℤ) ≤ ⌊(q:ℝ)/2⌋ := Int.floor_le_floor hcase.le
      omega
    have hbnd : ∀ d ∈ (Finset.Ioc (0:ℤ) ⌊(q:ℝ)/2⌋).filter (fun d : ℤ => Odd d),
        W' d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then 2*(q:ℝ)*Cb
                else min (2*(q:ℝ)*Cb) (Cb / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hd
      obtain ⟨⟨hd1, hd2⟩, hdodd⟩ := hd
      have hdR : ((d : ℤ) : ℝ) ≤ (q : ℝ) / 2 := by
        have h1 : ((d:ℤ):ℝ) ≤ ((⌊(q:ℝ)/2⌋ : ℤ) : ℝ) := by exact_mod_cast hd2
        linarith [Int.floor_le ((q:ℝ)/2)]
      have hdnat : 2 * d.toNat ≤ q := by
        have hz : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
        have h2 : (2:ℝ) * ((d.toNat : ℕ):ℝ) ≤ (q:ℝ) := by
          have : ((d.toNat : ℕ):ℝ) = ((d:ℤ):ℝ) := by exact_mod_cast congrArg (fun z : ℤ => (z:ℝ)) hz
          rw [this]; linarith
        exact_mod_cast h2
      have hsep := (TaoFivePrimes.sin_lower_bound_small_divisor alpha beta a q (by omega) haq
        halpha hbeta d.toNat (by omega) hdnat).2
      have hcast : ((d.toNat : ℕ) : ℝ) = ((d : ℤ) : ℝ) := by
        have hz : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
      rw [hcast] at hsep
      have hform : 2 * Real.pi * ((d : ℤ) : ℝ) * alpha
          = Real.pi * (2 * alpha) * ((d : ℤ) : ℝ) := by ring
      rw [hform] at hsep
      have hsin : Real.sin (Real.pi * (2 * alpha) * ((d : ℤ) : ℝ)) ≠ 0 := by
        intro hz
        rw [hz, abs_zero] at hsep
        have : (0:ℝ) < 1 / (2 * (q:ℝ)) := by positivity
        linarith
      have habs : (0 : ℝ) < |Real.sin (Real.pi * (2 * alpha) * ((d : ℤ) : ℝ))| := abs_pos.mpr hsin
      have hquot : Cb / |Real.sin (Real.pi * (2 * alpha) * ((d : ℤ) : ℝ))| ≤ 2 * (q : ℝ) * Cb := by
        rw [div_le_iff₀ habs]
        have h1 : 2 * (q : ℝ) * Cb * (1 / (2 * (q : ℝ))) = Cb := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hsep
          (show (0:ℝ) ≤ 2 * (q : ℝ) * Cb by positivity), h1]
      rw [if_neg hsin]
      rw [hW'def]; dsimp only
      by_cases hcond : 0 < d ∧ Odd d ∧ d ≤ ⌊U * V⌋
      · rw [if_pos hcond]
        obtain ⟨hpos, hodd, hle⟩ := hcond
        have hdM : ((d:ℤ):ℝ) ≤ U * V := le_trans (by exact_mod_cast hle) (Int.floor_le _)
        have hW := hW'b d hd1 hdM
        rw [hW'def] at hW; dsimp only at hW
        rw [if_pos ⟨hpos, hodd, hle⟩, if_neg hsin] at hW
        exact le_min (le_trans (le_trans hW (min_le_right _ _)) hquot)
          (le_trans hW (min_le_right _ _))
      · rw [if_neg hcond]
        exact le_min (by positivity) (by positivity)
    have hstep1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hW'0 d)
    have hstep2 := Finset.sum_le_sum hbnd
    have himp := TaoFivePrimes.typeI_small_divisor_contribution (2*(q:ℝ)*Cb) Cb alpha beta a q
      (by omega) (by positivity) hCb0 halpha hbeta
      (fun a1 a2 a3 a4 a5 a6 h1 h2 h3 => hvino (2*(q:ℝ)*Cb) a1 a2 a3 a4 a5 a6 (by positivity) h1 h2 h3)
    have hnum := numeric (q:ℝ) (U * V) (Real.log (q:ℝ)) (Real.log (2*x)) Cb 0
      (1 / Real.pi) (Real.log (4 * (q:ℝ)))
      hqR hM0 hLq hT0 hCb0 hCbub (by positivity) le_rfl hp0 hpub hG0 hGub
    linarith [hstep1, hstep2, himp, hnum, hfirst0]

end TaoTIB
end PartTI

theorem solution
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUV : U * V ≤ x / 4)
    (hvino : ∀ (A' alpha' beta' theta' u v : ℝ) (a' : ℤ), 0 ≤ A' →
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
              else min A' (4 * Real.log 2 * Real.log (2 * x)
                / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A' + (2 / Real.pi) * (4 * Real.log 2 * Real.log (2 * x)) * (q : ℝ)
                  * Real.log (4 * q)))
    (W : ℕ → ℝ) (hW0 : ∀ d, 0 ≤ W d)
    (hWb : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V,
        W d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                  (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
                else min ((1 / 2) * (x / (d : ℝ)) * Real.log x
                    + 4 * Real.log 2 * Real.log (2 * x))
                  (4 * Real.log 2 * Real.log (2 * x)
                    / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d)
      ≤ (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) :=
  TaoTIB.block_summation alpha beta a q hq haq halpha hbeta x U V hx hU40 hV40 hUV hvino W hW0 hWb
