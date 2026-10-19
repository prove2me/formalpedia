-- Prove2me | solution 1 for QAlgorithms.Nannicini.iterativePhaseEstimation_digits
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:15:09.10427+00:00
-- url     : https://prove2.me/submissions/86ea98d8-a3a6-49c3-baf3-1e23a6bdc187

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Mathlib.Tactic.IntervalCases

open QAlgorithms

private lemma cd_bound (x y : ℝ) (k : ℤ) : circDist x y ≤ |x - y - k| :=
  round_le (x-y) k

private lemma cd_triangle (x y z : ℝ) : circDist x z ≤ circDist x y + circDist y z := by
  apply (cd_bound x z (round (x-y) + round (y-z))).trans
  push_cast
  calc
    |x-z-((round (x-y) : ℝ) + round (y-z))| =
      |(x-y-round (x-y)) + (y-z-round (y-z))| := by ring_nf
    _ ≤ _ := abs_add_le _ _

private lemma cd_symm (x y : ℝ) : circDist x y = circDist y x := by
  apply le_antisymm
  · have h := cd_bound x y (-round (y-x))
    simpa only [circDist, Int.cast_neg, sub_neg_eq_add, show x-y+(round (y-x) : ℝ) =
      -(y-x-round (y-x)) by ring, abs_neg] using h
  · have h := cd_bound y x (-round (x-y))
    simpa only [circDist, Int.cast_neg, sub_neg_eq_add, show y-x+(round (x-y) : ℝ) =
      -(x-y-round (x-y)) by ring, abs_neg] using h

private lemma cd_close (x y : ℝ) : circDist x y ≤ |x-y| := by
  simpa using cd_bound x y 0

private lemma cd_half (x : ℝ) : circDist x (x+1/2) = 1/2 := by
  norm_num [circDist, show x-(x+1/2) = -(1/2:ℝ) by ring, round_neg_two_inv]

private lemma step_bound (y x w q e : ℝ) (he : e ≤ 1/8)
    (hy : circDist y (2*x) ≤ e) (hw : circDist w x ≤ 1/16)
    (hq : |y/2-q| < 1/8) :
    circDist ((if circDist q w < 1/4 then 0 else 1)/2+y/2) x ≤ e/2 := by
  let r : ℤ := round (y-2*x)
  have hr : |y-2*x-(r:ℝ)| ≤ e := hy
  have hp := Int.emod_nonneg r (by norm_num : (2:ℤ) ≠ 0)
  have hp' := Int.emod_lt_of_pos r (by norm_num : (0:ℤ) < 2)
  have hd := Int.emod_add_mul_ediv r 2
  have cases : r % 2 = 0 ∨ r % 2 = 1 := by omega
  have separated : ¬ (circDist q w < 1/4 ∧ circDist (q+1/2) w < 1/4) := by
    rintro ⟨h0,h1⟩
    have h := cd_triangle q w (q+1/2)
    rw [cd_half, cd_symm w] at h
    linarith
  have auxiliary (b : ℝ) (k : ℤ) (hk : (r:ℝ) = 2*(k:ℝ) - b) :
      circDist (b/2+y/2) x ≤ e/2 ∧ circDist (q+b/2) w < 1/4 := by
    have hb : circDist (b/2+y/2) x ≤ e/2 := by
      apply (cd_bound _ _ k).trans
      calc
        |b/2+y/2-x-(k:ℝ)| = |y-2*x-(r:ℝ)|/2 := by
          rw [show b/2+y/2-x-(k:ℝ) = (y-2*x-(r:ℝ))/2 by linarith, abs_div]
          norm_num
        _ ≤ e/2 := by linarith
    refine ⟨hb, ?_⟩
    have h1 := cd_triangle (q+b/2) (b/2+y/2) x
    have h2 := cd_triangle (q+b/2) x w
    have hc := cd_close (q+b/2) (b/2+y/2)
    rw [cd_symm x w] at h2
    have habs : |q+b/2-(b/2+y/2)| = |y/2-q| := by
      rw [show q+b/2-(b/2+y/2) = -(y/2-q) by ring, abs_neg]
    rw [habs] at hc
    linarith
  rcases cases with h | h
  · have hr0 : r = 2*(r/2) := by omega
    have ha := auxiliary 0 (r/2) (by simpa only [sub_zero] using (show (r:ℝ) = 2*(r/2:ℤ) by exact_mod_cast hr0))
    norm_num at ha
    rw [if_pos ha.2]
    simpa only [zero_div, zero_add] using ha.1
  · have hr1 : r = 2*(r/2+1)-1 := by omega
    have ha := auxiliary 1 (r/2+1) (by exact_mod_cast hr1)
    have hn : ¬ circDist q w < 1/4 := fun h0 => separated ⟨h0, ha.2⟩
    rw [if_neg hn]
    exact ha.1

private lemma frac_step (p : ℕ → Bool) (j last : ℕ) (hj : j ≤ last) :
    binFracFrom p j last = (if p j then 1 else 0)/2 + binFracFrom p (j+1) last / 2 := by
  have hs : Finset.Icc j last = insert j (Finset.Icc (j+1) last) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  unfold binFracFrom
  rw [hs, Finset.sum_insert (by simp)]
  simp only [Nat.sub_self, zero_add, pow_one]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := (Finset.mem_Icc.mp hi).1
  have he : i-j+1 = (i-(j+1)+1)+1 := by omega
  rw [he, pow_succ, mul_inv]
  ring

private lemma frac_nonneg (p : ℕ → Bool) (j last : ℕ) : 0 ≤ binFracFrom p j last := by
  unfold binFracFrom
  apply Finset.sum_nonneg
  intro i hi
  positivity

private lemma frac_lt_one (p : ℕ → Bool) (j last : ℕ) : binFracFrom p j last < 1 := by
  have aux : ∀ k j, binFracFrom p j (j+k) < 1 := by
    intro k
    induction k with
    | zero => intro j; simp [binFracFrom]; split_ifs <;> norm_num
    | succ k ih =>
      intro j
      rw [frac_step p j (j+(k+1)) (by omega)]
      have hh := ih (j+1)
      rw [show j+(k+1) = (j+1)+k by omega]
      split_ifs <;> linarith
  by_cases h : j ≤ last
  · simpa [Nat.add_sub_of_le h] using aux (last-j) j
  · simp [binFracFrom, Finset.Icc_eq_empty_of_lt (by omega : last < j)]

private lemma frac_tail (p : ℕ → Bool) (j last : ℕ) (hj : j+2 ≤ last) :
    |binFracFrom p (j+1) last / 2 -
      ((if p (j+1) then 1 else 0)/4 + (if p (j+2) then 1 else 0)/8)| < 1/8 := by
  rw [frac_step p (j+1) last (by omega), frac_step p (j+2) last hj]
  have hn := frac_nonneg p (j+3) last
  have hl := frac_lt_one p (j+3) last
  have he : ((if p (j+1) then (1:ℝ) else 0)/2 +
      ((if p (j+2) then 1 else 0)/2 + binFracFrom p (j+3) last / 2)/2)/2 -
      ((if p (j+1) then 1 else 0)/4 + (if p (j+2) then 1 else 0)/8) =
      binFracFrom p (j+3) last / 8 := by ring
  rw [show j+1+1 = j+2 by omega, show j+2+1 = j+3 by omega, he,
    abs_of_nonneg (by positivity)]
  linarith

private lemma first_digit (h : ℕ) (ω : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (jh : j ≤ h) :
    (ipeLowPair h ω (h-j)).1 = ipeDigits h ω j := by
  simp [ipeDigits, show j ≠ h+2 by omega, show j ≠ h+1 by omega, hj, jh]

private lemma pair_digits (h : ℕ) (ω : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (jh : j ≤ h) :
    ipeLowPair h ω (h-j) = (ipeDigits h ω j, ipeDigits h ω (j+1)) := by
  apply Prod.ext
  · exact first_digit h ω j hj jh
  · cases hd : h-j with
    | zero =>
      have hh : j = h := by omega
      subst j
      simp [ipeLowPair, ipeDigits]
    | succ d =>
      change (ipeLowPair h ω d).1 = ipeDigits h ω (j+1)
      have he : d = h-(j+1) := by omega
      rw [he]
      exact first_digit h ω (j+1) (by omega) (by omega)

private lemma digit_step (h : ℕ) (ω : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (jh : j < h) :
    ipeDigits h ω j =
      if circDist ((if ipeDigits h ω (j+1) then 1 else 0)/4 +
        (if ipeDigits h ω (j+2) then 1 else 0)/8) (ω j) < 1/4 then false else true := by
  rw [← first_digit h ω j hj (by omega)]
  have he : h-j = (h-(j+1))+1 := by omega
  rw [he, ipeLowPair, pair_digits h ω (j+1) (by omega) (by omega)]
  simp only [show h-(h-(j+1))-1 = j by omega, show j+1+1 = j+2 by omega,
    div_eq_mul_inv, one_mul]

private lemma init_frac (h : ℕ) (ω : ℕ → ℝ) (hh : 1 ≤ h) :
    binFracFrom (ipeDigits h ω) h (h+2) = (ipeInitIndex h ω : ℝ)/8 := by
  rw [frac_step _ h (h+2) (by omega), frac_step _ (h+1) (h+2) (by omega),
    frac_step _ (h+1+1) (h+2) (by omega)]
  have hempty : binFracFrom (ipeDigits h ω) (h+1+1+1) (h+2) = 0 := by
    simp [binFracFrom]
  rw [hempty]
  simp only [ipeDigits, show h ≠ h+2 by omega, show h ≠ h+1 by omega,
    show h+1 ≠ h+2 by omega, show h+1+1 = h+2 by omega, if_false, if_true,
    Nat.sub_self, ipeLowPair, hh, le_refl, and_self, zero_div, add_zero]
  have hk : ipeInitIndex h ω < 8 := by
    unfold ipeInitIndex
    have h0 := Int.emod_nonneg (round (8 * ω h)) (by norm_num : (8:ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos (round (8 * ω h)) (by norm_num : (0:ℤ)<8)
    omega
  generalize ipeInitIndex h ω = k at *
  interval_cases k <;> norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]

private lemma init_bound (h : ℕ) (ω : ℕ → ℝ) :
    circDist ((ipeInitIndex h ω : ℝ)/8) (ω h) ≤ 1/16 := by
  let r : ℤ := round (8*ω h)
  have hp := Int.emod_nonneg r (by norm_num : (8:ℤ) ≠ 0)
  have hd := Int.emod_add_mul_ediv r 8
  have hk : (ipeInitIndex h ω : ℝ) = (r:ℝ)-8*(r/8:ℤ) := by
    have hc : (ipeInitIndex h ω : ℤ) = r % 8 := Int.toNat_of_nonneg hp
    have hx : (ipeInitIndex h ω : ℤ) = r-8*(r/8) := by omega
    exact_mod_cast hx
  apply (cd_bound _ _ (-(r/8))).trans
  rw [hk]
  have he : ((r:ℝ)-8*(r/8:ℤ))/8-ω h-(-(r/8):ℤ) = -((8*ω h-(r:ℝ))/8) := by
    push_cast
    ring
  rw [he, abs_neg, abs_div]
  have hb := abs_sub_round (8*ω h)
  norm_num at *
  linarith

theorem solution (φ : ℝ) (_hφ0 : 0 ≤ φ) (_hφ1 : φ < 1) (h : ℕ)
    (ω : ℕ → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ h)
    (hω : ∀ i, j ≤ i → i ≤ h → circDist (ω i) ((2 : ℝ) ^ (i - 1) * φ) ≤ 1 / 16) :
    circDist (binFracFrom (ipeDigits h ω) j (h + 2)) ((2 : ℝ) ^ (j - 1) * φ) ≤
      ((2 : ℝ) ^ (h + 3 - j))⁻¹ := by
  have aux : ∀ d : ℕ, d ≤ h-j →
      circDist (binFracFrom (ipeDigits h ω) (h-d) (h+2))
        ((2:ℝ)^(h-d-1)*φ) ≤ ((2:ℝ)^(d+3))⁻¹ := by
    intro d
    induction d with
    | zero =>
      intro hd
      simp only [Nat.sub_zero, zero_add]
      rw [init_frac h ω (by omega)]
      have ht := cd_triangle ((ipeInitIndex h ω : ℝ)/8) (ω h) ((2:ℝ)^(h-1)*φ)
      have hi := init_bound h ω
      have hw := hω h hjh (le_refl _)
      norm_num
      linarith
    | succ d ih =>
      intro hd
      have ih' := ih (by omega)
      let k := h-(d+1)
      have hk1 : 1 ≤ k := by dsimp [k]; omega
      have hkh : k < h := by dsimp [k]; omega
      have hkj : j ≤ k := by dsimp [k]; omega
      have heq : h-d = k+1 := by dsimp [k]; omega
      have hpow : (2:ℝ)^(h-d-1)*φ = 2*((2:ℝ)^(k-1)*φ) := by
        rw [heq, show k+1-1 = (k-1)+1 by omega, pow_succ]
        ring
      rw [hpow, heq] at ih'
      have he : ((2:ℝ)^(d+3))⁻¹ ≤ 1/8 := by
        have ht : (2:ℝ)^3 ≤ 2^(d+3) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hx := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2^3) ht
        norm_num [one_div] at hx ⊢
        exact hx
      have hs := step_bound (binFracFrom (ipeDigits h ω) (k+1) (h+2))
        ((2:ℝ)^(k-1)*φ) (ω k)
        ((if ipeDigits h ω (k+1) then 1 else 0)/4 +
          (if ipeDigits h ω (k+2) then 1 else 0)/8)
        ((2:ℝ)^(d+3))⁻¹ he ih' (hω k hkj (by omega))
        (frac_tail _ k (h+2) (by omega))
      change circDist (binFracFrom (ipeDigits h ω) k (h+2))
        ((2:ℝ)^(k-1)*φ) ≤ ((2:ℝ)^(d+1+3))⁻¹
      rw [frac_step _ k (h+2) (by omega), digit_step h ω k hk1 hkh]
      have he2 : ((2:ℝ)^(d+1+3))⁻¹ = ((2:ℝ)^(d+3))⁻¹/2 := by
        rw [show d+1+3 = (d+3)+1 by omega, pow_succ, mul_inv]
        ring
      rw [he2]
      by_cases hc : circDist ((if ipeDigits h ω (k+1) then 1 else 0)/4 +
          (if ipeDigits h ω (k+2) then 1 else 0)/8) (ω k) < 1/4
      · simpa only [hc, if_true, if_false, Bool.false_eq_true] using hs
      · simpa only [hc, if_true, if_false, Bool.false_eq_true] using hs
  have ht := aux (h-j) (le_refl _)
  have heq : h-(h-j) = j := by omega
  have hexp : h-j+3 = h+3-j := by omega
  simpa only [heq, hexp] using ht
