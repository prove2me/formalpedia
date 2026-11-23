-- Prove2me | solution 1 for TIESharp.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:30:17.560746+00:00
-- url     : https://prove2.me/submissions/9c191e0c-41e5-401c-abe1-08016a76d0a2

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Lemma 5.7: reduction of the two-variable cost region to its two kinds of ray endpoints. -/
theorem solution (θ : Fin 7 → ℝ) (hθnn : ∀ l, 0 ≤ θ l) (hθsum : ∑ l, θ l = 1)
    (hθ₁ : 3 / 4 < Real.sqrt (∑ l, θ l ^ 2)) (hθ₂ : Real.sqrt (∑ l, θ l ^ 2) < 1)
    (i k : Fin 7) (hi : ∀ l, θ l ≤ θ i) (hki : k ≠ i)
    (d s : ℝ) (hd : 1 ≤ d) (hs₁ : d / 2 ≤ s) (hs₂ : s ≤ 1)
    (H : ∀ d' ∈ Set.Icc (1 : ℝ) 2,
      (2 - d') * θ i * (1 - θ i)
        + (max ((d' + 1) * θ i - Real.sqrt (∑ l, θ l ^ 2) - 1) 0) ^ 2
          / (4 * ((d' ^ 2 + 1) * Real.sqrt (∑ l, θ l ^ 2) + 1 - (d' + 1) * θ i))
        ≥ 2 * (1 - Real.sqrt (∑ l, θ l ^ 2)) * (Real.sqrt (∑ l, θ l ^ 2) - 3 / 4)) :
    (2 - d) * θ i * (1 - θ i)
      + s * (max (d * θ i - s * (Real.sqrt (∑ l, θ l ^ 2) + θ k)) 0) ^ 2
        / (4 * ((d ^ 2 + s ^ 2) * Real.sqrt (∑ l, θ l ^ 2) - d * s * θ i + s ^ 2 * θ k))
      ≥ 2 * (1 - Real.sqrt (∑ l, θ l ^ 2)) * (Real.sqrt (∑ l, θ l ^ 2) - 3 / 4) := by
  set r : ℝ := Real.sqrt (∑ l, θ l ^ 2) with hr_def
  set a : ℝ := θ i with ha_def
  set b : ℝ := θ k with hb_def
  have ha0 : 0 ≤ a := hθnn i
  have hb0 : 0 ≤ b := hθnn k
  have hr0 : 0 < r := by linarith
  have hr_sq : r ^ 2 = ∑ l, θ l ^ 2 := by
    rw [hr_def]
    exact Real.sq_sqrt (Finset.sum_nonneg fun l _ => sq_nonneg (θ l))
  have ha_le_sum : a ≤ ∑ l, θ l := by
    rw [ha_def]
    exact Finset.single_le_sum (fun l _ => hθnn l) (Finset.mem_univ i)
  have ha1 : a ≤ 1 := by rwa [hθsum] at ha_le_sum
  have ha_sq_le : a ^ 2 ≤ ∑ l, θ l ^ 2 := by
    rw [ha_def]
    exact Finset.single_le_sum (fun l _ => sq_nonneg (θ l)) (Finset.mem_univ i)
  have har : a ≤ r := by
    have ha2r2 : a ^ 2 ≤ r ^ 2 := by rwa [hr_sq]
    nlinarith
  have hsq_le_a : ∑ l, θ l ^ 2 ≤ a := by
    calc
      ∑ l, θ l ^ 2 = ∑ l, θ l * θ l := by congr 1 with l; ring
      _ ≤ ∑ l, a * θ l := by
        apply Finset.sum_le_sum
        intro l hl
        exact mul_le_mul_of_nonneg_right (hi l) (hθnn l)
      _ = a * ∑ l, θ l := by rw [Finset.mul_sum]
      _ = a := by rw [hθsum, mul_one]
  have hr2a : r ^ 2 ≤ a := by rwa [hr_sq]
  have hbase : 2 * (1 - r) * (r - 3 / 4) ≤ a * (1 - a) := by
    have hquad : 2 * (r - 3 / 4) ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
    have hmul := mul_le_mul_of_nonneg_left hquad (sub_nonneg.mpr hθ₂.le)
    have hprod₁ : r ^ 2 * (1 - r) ≤ a * (1 - r) :=
      mul_le_mul_of_nonneg_right hr2a (sub_nonneg.mpr hθ₂.le)
    have hprod₂ : a * (1 - r) ≤ a * (1 - a) :=
      mul_le_mul_of_nonneg_left (by linarith) ha0
    nlinarith
  have hden : ∀ {D S : ℝ}, 0 < D → 0 < S →
      0 < (D ^ 2 + S ^ 2) * r - D * S * a + S ^ 2 * b := by
    intro D S hD hS
    have hquad : 0 < D ^ 2 - D * S + S ^ 2 := by
      nlinarith [sq_nonneg (D - S), mul_pos hD hS]
    have hcomp : D * S * a ≤ D * S * r :=
      mul_le_mul_of_nonneg_left har (mul_nonneg hD.le hS.le)
    have hbterm : 0 ≤ S ^ 2 * b := mul_nonneg (sq_nonneg S) hb0
    have hpos := mul_pos hr0 hquad
    nlinarith
  have hd0 : 0 < d := by linarith
  have hs0 : 0 < s := by linarith
  have hsd : s ≤ d := hs₂.trans hd
  let T : ℝ := s * (max (d * a - s * (r + b)) 0) ^ 2 /
    (4 * ((d ^ 2 + s ^ 2) * r - d * s * a + s ^ 2 * b))
  let B : ℝ := T - d * a * (1 - a)
  have hscale_max (lam : ℝ) (hlam : 0 < lam) :
      max ((lam * d) * a - (lam * s) * (r + b)) 0 =
        lam * max (d * a - s * (r + b)) 0 := by
    have hfactor : (lam * d) * a - (lam * s) * (r + b) =
        lam * (d * a - s * (r + b)) := by ring
    rw [hfactor]
    by_cases hmax : 0 ≤ d * a - s * (r + b)
    · rw [max_eq_left hmax, max_eq_left (mul_nonneg hlam.le hmax)]
    · have hmax' : d * a - s * (r + b) ≤ 0 := le_of_not_ge hmax
      rw [max_eq_right hmax', max_eq_right (mul_nonpos_of_nonneg_of_nonpos hlam.le hmax'),
        mul_zero]
  have hkey (lam : ℝ) (hlam : 0 < lam) :
      (2 - lam * d) * a * (1 - a) +
          (lam * s) * (max ((lam * d) * a - (lam * s) * (r + b)) 0) ^ 2 /
            (4 * (((lam * d) ^ 2 + (lam * s) ^ 2) * r -
              (lam * d) * (lam * s) * a + (lam * s) ^ 2 * b)) =
        2 * a * (1 - a) + lam * B := by
    have hD := hden hd0 hs0
    have hDlam : 0 < ((lam * d) ^ 2 + (lam * s) ^ 2) * r -
        (lam * d) * (lam * s) * a + (lam * s) ^ 2 * b :=
      hden (mul_pos hlam hd0) (mul_pos hlam hs0)
    rw [hscale_max lam hlam]
    dsimp [B, T]
    field_simp [ne_of_gt hlam, ne_of_gt hD, ne_of_gt hDlam]
    ring
  have hlow : 2 * (1 - r) * (r - 3 / 4) ≤
      (2 - (1 / d) * d) * a * (1 - a) +
        ((1 / d) * s) * (max (((1 / d) * d) * a - ((1 / d) * s) * (r + b)) 0) ^ 2 /
          (4 * ((((1 / d) * d) ^ 2 + ((1 / d) * s) ^ 2) * r -
            ((1 / d) * d) * ((1 / d) * s) * a + ((1 / d) * s) ^ 2 * b)) := by
    have hsd0 : 0 < s / d := div_pos hs0 hd0
    have hDlow := hden one_pos hsd0
    have hfracnn : 0 ≤ (s / d) * (max (1 * a - (s / d) * (r + b)) 0) ^ 2 /
        (4 * ((1 ^ 2 + (s / d) ^ 2) * r - 1 * (s / d) * a + (s / d) ^ 2 * b)) :=
      div_nonneg (mul_nonneg hsd0.le (sq_nonneg _)) (by positivity)
    have hd_cancel : (1 / d) * d = 1 := by field_simp
    have hs_eq : (1 / d) * s = s / d := by ring
    rw [hd_cancel, hs_eq]
    norm_num at hfracnn ⊢
    linarith
  have hup : 2 * (1 - r) * (r - 3 / 4) ≤
      (2 - (1 / s) * d) * a * (1 - a) +
        ((1 / s) * s) * (max (((1 / s) * d) * a - ((1 / s) * s) * (r + b)) 0) ^ 2 /
          (4 * ((((1 / s) * d) ^ 2 + ((1 / s) * s) ^ 2) * r -
            ((1 / s) * d) * ((1 / s) * s) * a + ((1 / s) * s) ^ 2 * b)) := by
    let u : ℝ := d / s
    have hu0 : 0 < u := div_pos hd0 hs0
    have hu1 : 1 ≤ u := (le_div_iff₀ hs0).2 (by simpa using hsd)
    have hu2 : u ≤ 2 := (div_le_iff₀ hs0).2 (by linarith)
    have hpair : a + b ≤ 1 := by
      have hsum : θ i + θ k ≤ ∑ l, θ l := by
        have hsub : ({i, k} : Finset (Fin 7)) ⊆ Finset.univ := Finset.subset_univ _
        have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun l _ _ => hθnn l)
        simpa [hki.symm] using hs
      rw [hθsum] at hsum
      exact hsum
    have hDu : 0 < (u ^ 2 + 1) * r - u * a + b := by
      have := hden hu0 one_pos
      nlinarith
    have hDv : 0 < (u ^ 2 + 1) * r + 1 - (u + 1) * a := by
      nlinarith
    have hnum : (max ((u + 1) * a - r - 1) 0) ^ 2 ≤
        (max (u * a - (r + b)) 0) ^ 2 := by
      have hle : max ((u + 1) * a - r - 1) 0 ≤ max (u * a - (r + b)) 0 := by
        apply max_le_max _ le_rfl
        nlinarith
      have hn0 : 0 ≤ max ((u + 1) * a - r - 1) 0 := le_max_right _ _
      have hn1 : 0 ≤ max (u * a - (r + b)) 0 := le_max_right _ _
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hn0 hn1)]
    have hden_le : (u ^ 2 + 1) * r - u * a + b ≤
        (u ^ 2 + 1) * r + 1 - (u + 1) * a := by nlinarith
    have hfrac : (max ((u + 1) * a - r - 1) 0) ^ 2 /
          (4 * ((u ^ 2 + 1) * r + 1 - (u + 1) * a)) ≤
        (max (u * a - (r + b)) 0) ^ 2 / (4 * ((u ^ 2 + 1) * r - u * a + b)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * ((u ^ 2 + 1) * r + 1 - (u + 1) * a))
        (by positivity : 0 < 4 * ((u ^ 2 + 1) * r - u * a + b))).2
      calc
        (max ((u + 1) * a - r - 1) 0) ^ 2 * (4 * ((u ^ 2 + 1) * r - u * a + b))
            ≤ (max (u * a - (r + b)) 0) ^ 2 * (4 * ((u ^ 2 + 1) * r - u * a + b)) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
        _ ≤ (max (u * a - (r + b)) 0) ^ 2 * (4 * ((u ^ 2 + 1) * r + 1 - (u + 1) * a)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    have hHu := H u ⟨hu1, hu2⟩
    have hs_cancel : (1 / s) * s = 1 := by field_simp
    have hu_eq : (1 / s) * d = u := by dsimp [u]; ring
    rw [hs_cancel, hu_eq]
    norm_num
    exact hHu.trans (add_le_add_right hfrac ((2 - u) * a * (1 - a)))
  by_cases hB : 0 ≤ B
  · have hlo_lam : (1 / d) ≤ 1 := (div_le_one hd0).2 hd
    have hlowkey := hkey (1 / d) (by positivity)
    have horigkey := hkey 1 one_pos
    have hstep : 2 * a * (1 - a) + (1 / d) * B ≤ 2 * a * (1 - a) + 1 * B := by
      linarith [mul_le_mul_of_nonneg_right hlo_lam hB]
    norm_num at horigkey
    linarith
  · have hB' : B ≤ 0 := le_of_not_ge hB
    have hup_lam : 1 ≤ (1 / s) := (le_div_iff₀ hs0).2 (by simpa using hs₂)
    have hupkey := hkey (1 / s) (by positivity)
    have horigkey := hkey 1 one_pos
    have hstep : 2 * a * (1 - a) + 1 * B ≥ 2 * a * (1 - a) + (1 / s) * B := by
      have := mul_le_mul_of_nonpos_right hup_lam hB'
      linarith
    norm_num at horigkey
    linarith
