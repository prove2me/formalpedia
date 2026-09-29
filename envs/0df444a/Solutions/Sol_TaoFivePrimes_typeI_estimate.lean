-- Prove2me | solution 1 for TaoFivePrimes.typeI_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:45:49.569457+00:00
-- url     : https://prove2.me/submissions/f099d6bd-f9ba-462a-8529-315ad64893c8

import Mathlib
import Theorems.Thm_TaoFivePrimes_vinogradov_odd
import Theorems.Thm_TaoFivePrimes_sin_lower_bound_small_divisor
import Theorems.Thm_TaoFivePrimes_typeI_block_sum_bound
import Theorems.Thm_TaoFivePrimes_typeI_small_divisor_contribution

open Finset

section PartS5T
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
  ∀ (A' alpha' beta' theta' u v : ℝ) (a' : ℤ),
    alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))

/-- One block of length `2q`: Corollary 3.5 with block count `2`. -/
theorem block_bound (A B alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
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
    (by rw [← halpha]; ring) hbeta u v huv (hvino A)
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
      a q hq (by positivity) hCb halpha hbeta (hvino (2 * (q : ℝ) * Cb))
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
      exact block_bound (Aj j) Cb alpha beta a q (by omega) halpha hbeta hvino _
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
end PartS5T

theorem solution
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x M Lx Cb : ℝ) (hx : 0 < x) (hLx : 0 ≤ Lx) (hCb : 0 ≤ Cb) (hM : (q : ℝ) / 2 ≤ M)
    (hvino : ∀ (A' alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
              else min A' (Cb / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A' + (2 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q)))
    (W : ℤ → ℝ) (hW0 : ∀ d, 0 ≤ W d)
    (hWb : ∀ d : ℤ, 1 ≤ d → (d : ℝ) ≤ M →
        W d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                  (1 / 2) * (x / (d : ℝ)) * Lx + Cb
                else min ((1 / 2) * (x / (d : ℝ)) * Lx + Cb)
                  (Cb / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    (∑ d ∈ (Finset.Ioc (0 : ℤ) ⌊M⌋).filter (fun d : ℤ => Odd d), W d)
      ≤ (2 * (q : ℝ) * Cb + (1 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q))
        + ((x / q) * Lx * (Real.log (2 * M / q + 4) + 4)
           + ((⌊M / (2 * (q : ℝ)) - 1 / 4⌋₊ : ℝ) + 1)
               * (4 * Cb + (4 / Real.pi) * Cb * (q : ℝ) * Real.log (4 * q))) :=
  TaoS5T.typeI_total alpha beta a q hq haq halpha hbeta x M Lx Cb hx hLx hCb hM hvino W hW0 hWb
