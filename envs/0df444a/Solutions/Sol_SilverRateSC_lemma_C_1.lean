-- Prove2me | solution 1 for SilverRateSC.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:52:26.154364+00:00
-- url     : https://prove2.me/submissions/50f718c7-aa6c-447b-98c0-605dca6b2688

import Mathlib

namespace SolSilverRateCOne

open Finset

/-- The Claim in the proof of Lemma C.1: a segment `[l, u)` of nonnegative reals in which no two
`τ`-large entries are separated by a gap of mass at most the smaller of them, and whose large
entries are dominated by the mass on their left (`lf`) and/or right (`rf`), has total mass at most
`τ n²` (both sides) or `2 τ n²` (one side), where `n = u - l`. -/
theorem claim (h : ℕ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∀ (n : ℕ) (lf rf : Bool) (l u : ℕ), (lf = true ∨ rf = true) → u = l + n →
      (∀ t ∈ Ico l u, 0 ≤ h t) →
      (∀ i j, l ≤ i → i < j → j < u → τ ≤ h i → τ ≤ h j →
          min (h i) (h j) < ∑ v ∈ Ico (i+1) j, h v) →
      (∀ i, l ≤ i → i < u → τ ≤ h i →
          (lf = true → h i < ∑ v ∈ Ico l i, h v) ∧
          (rf = true → h i < ∑ v ∈ Ico (i+1) u, h v)) →
      ∑ v ∈ Ico l u, h v ≤ (if lf = true ∧ rf = true then 1 else 2) * τ * (n:ℝ)^2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lf rf l u hlr hu hnn h46 hflag
  have hcoef : (1:ℝ) ≤ (if lf = true ∧ rf = true then 1 else 2) := by split_ifs <;> norm_num
  by_cases hsmall : ∀ t ∈ Ico l u, h t < τ
  · have h1 : ∑ v ∈ Ico l u, h v ≤ ∑ v ∈ Ico l u, τ :=
      sum_le_sum fun t ht => (hsmall t ht).le
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul, show u - l = n by omega] at h1
    have hn : (n:ℝ) ≤ (n:ℝ)^2 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · simp [h0]
      · have : (1:ℝ) ≤ n := by exact_mod_cast h0
        nlinarith
    calc ∑ v ∈ Ico l u, h v ≤ n * τ := h1
      _ ≤ 1 * τ * (n:ℝ)^2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hτ) (sq_nonneg _)
  · push Not at hsmall
    obtain ⟨t, ht, hτt⟩ := hsmall
    obtain ⟨z, hz, hzmax⟩ := exists_max_image (Ico l u) h ⟨t, ht⟩
    rw [mem_Ico] at hz
    have hbτ : τ ≤ h z := le_trans hτt (hzmax t ht)
    have hsplit : ∑ v ∈ Ico l u, h v
        = ∑ v ∈ Ico l z, h v + h z + ∑ v ∈ Ico (z+1) u, h v := by
      rw [← sum_Ico_consecutive _ hz.1 hz.2.le, sum_eq_sum_Ico_succ_bot hz.2]; ring
    have hLnn : ∀ t ∈ Ico l z, 0 ≤ h t := fun t ht => hnn t (by rw [mem_Ico] at ht ⊢; omega)
    have hL46 : ∀ i j, l ≤ i → i < j → j < z → τ ≤ h i → τ ≤ h j →
        min (h i) (h j) < ∑ v ∈ Ico (i+1) j, h v :=
      fun i j h1 h2 h3 => h46 i j h1 h2 (by omega)
    have hLright : ∀ i, l ≤ i → i < z → τ ≤ h i → h i < ∑ v ∈ Ico (i+1) z, h v := by
      intro i h1 h2 h3
      have := h46 i z h1 h2 hz.2 h3 hbτ
      rwa [min_eq_left (hzmax i (by rw [mem_Ico]; omega))] at this
    have hRnn : ∀ t ∈ Ico (z+1) u, 0 ≤ h t := fun t ht => hnn t (by rw [mem_Ico] at ht ⊢; omega)
    have hR46 : ∀ i j, z+1 ≤ i → i < j → j < u → τ ≤ h i → τ ≤ h j →
        min (h i) (h j) < ∑ v ∈ Ico (i+1) j, h v :=
      fun i j h1 h2 h3 => h46 i j (by omega) h2 h3
    have hRleft : ∀ i, z+1 ≤ i → i < u → τ ≤ h i → h i < ∑ v ∈ Ico (z+1) i, h v := by
      intro i h1 h2 h3
      have := h46 z i hz.1 (by omega) h2 hbτ h3
      rwa [min_eq_right (hzmax i (by rw [mem_Ico]; omega))] at this
    have hIL : ∀ lf' : Bool,
        (∀ i, l ≤ i → i < z → τ ≤ h i → lf' = true → h i < ∑ v ∈ Ico l i, h v) →
        ∑ v ∈ Ico l z, h v ≤ (if lf' = true ∧ true = true then 1 else 2) * τ * ((z - l : ℕ):ℝ)^2 := by
      intro lf' hlf'
      exact ih (z - l) (by omega) lf' true l z (Or.inr rfl) (by omega) hLnn hL46
        (fun i h1 h2 h3 => ⟨hlf' i h1 h2 h3, fun _ => hLright i h1 h2 h3⟩)
    have hIR : ∀ rf' : Bool,
        (∀ i, z+1 ≤ i → i < u → τ ≤ h i → rf' = true → h i < ∑ v ∈ Ico (i+1) u, h v) →
        ∑ v ∈ Ico (z+1) u, h v ≤ (if true = true ∧ rf' = true then 1 else 2) * τ
          * ((u - (z+1) : ℕ):ℝ)^2 := by
      intro rf' hrf'
      exact ih (u - (z+1)) (by omega) true rf' (z+1) u (Or.inl rfl) (by omega) hRnn hR46
        (fun i h1 h2 h3 => ⟨fun _ => hRleft i h1 h2 h3, hrf' i h1 h2 h3⟩)
    have hn : (n:ℝ) = ((z - l : ℕ):ℝ) + ((u - (z+1) : ℕ):ℝ) + 1 := by
      exact_mod_cast (by omega : n = (z - l) + (u - (z+1)) + 1)
    have hnL0 : (0:ℝ) ≤ ((z - l : ℕ):ℝ) := Nat.cast_nonneg _
    have hnR0 : (0:ℝ) ≤ ((u - (z+1) : ℕ):ℝ) := Nat.cast_nonneg _
    rw [hsplit, hn]
    have hzl := hflag z hz.1 hz.2 hbτ
    generalize ((z - l : ℕ):ℝ) = a at hIL hnL0 ⊢
    generalize ((u - (z+1) : ℕ):ℝ) = c at hIR hnR0 ⊢
    cases lf <;> cases rf
    · simp at hlr
    · have hb : h z < ∑ v ∈ Ico (z+1) u, h v := hzl.2 rfl
      have hL := hIL false (fun i _ _ _ h => absurd h (by simp))
      have hR := hIR true (fun i h1 h2 h3 _ => (hflag i (by omega) h2 h3).2 rfl)
      norm_num at hL hR ⊢
      nlinarith [mul_nonneg hτ (mul_nonneg hnL0 hnR0), mul_nonneg hτ hnL0, mul_nonneg hτ hnR0]
    · have hb : h z < ∑ v ∈ Ico l z, h v := hzl.1 rfl
      have hL := hIL true (fun i h1 h2 h3 _ => (hflag i h1 (by omega) h3).1 rfl)
      have hR := hIR false (fun i _ _ _ h => absurd h (by simp))
      norm_num at hL hR ⊢
      nlinarith [mul_nonneg hτ (mul_nonneg hnL0 hnR0), mul_nonneg hτ hnL0, mul_nonneg hτ hnR0]
    · have hb1 : h z < ∑ v ∈ Ico l z, h v := hzl.1 rfl
      have hb2 : h z < ∑ v ∈ Ico (z+1) u, h v := hzl.2 rfl
      have hL := hIL true (fun i h1 h2 h3 _ => (hflag i h1 (by omega) h3).1 rfl)
      have hR := hIR true (fun i h1 h2 h3 _ => (hflag i (by omega) h2 h3).2 rfl)
      norm_num at hL hR ⊢
      have hbmin : h z ≤ τ * (a * c) := by
        rcases le_total a c with hac | hac
        · have : τ * a ^ 2 ≤ τ * (a * c) := by
            apply mul_le_mul_of_nonneg_left _ hτ; nlinarith
          linarith
        · have : τ * c ^ 2 ≤ τ * (a * c) := by
            apply mul_le_mul_of_nonneg_left _ hτ; nlinarith
          linarith
      nlinarith [mul_nonneg hτ (mul_nonneg hnL0 hnR0), mul_nonneg hτ hnL0, mul_nonneg hτ hnR0]

end SolSilverRateCOne

open SolSilverRateCOne in
theorem solution (r : ℕ) (hr : 1 ≤ r) (h : ℕ → ℝ) (hh : ∀ t ∈ Finset.Icc 1 r, 0 ≤ h t)
    (hS : 0 < ∑ t ∈ Finset.Icc 1 r, h t) :
    (∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ r ∧
        (∑ t ∈ Finset.Icc 1 r, h t) / (8 * (r : ℝ) ^ 2) ≤ h i ∧
        (∑ t ∈ Finset.Icc 1 r, h t) / (8 * (r : ℝ) ^ 2) ≤ h j ∧
        ∑ t ∈ Finset.Ioo i j, h t ≤ min (h i) (h j)) ∨
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ r ∧ 3 * (∑ t ∈ Finset.Icc 1 r, h t) / 4 ≤ h i := by
  by_cases halt : ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ r ∧
        (∑ t ∈ Finset.Icc 1 r, h t) / (8 * (r : ℝ) ^ 2) ≤ h i ∧
        (∑ t ∈ Finset.Icc 1 r, h t) / (8 * (r : ℝ) ^ 2) ≤ h j ∧
        ∑ t ∈ Finset.Ioo i j, h t ≤ min (h i) (h j)
  · exact Or.inl halt
  right
  have hIcc : Finset.Icc 1 r = Finset.Ico 1 (r+1) := (Finset.Ico_add_one_right_eq_Icc 1 r).symm
  rw [hIcc] at hh hS ⊢
  rw [hIcc] at halt
  set S := ∑ t ∈ Finset.Ico 1 (r+1), h t with hSdef
  set τ := S / (8 * (r:ℝ)^2) with hτdef
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hτ : 0 ≤ τ := by positivity
  have hτr : τ * (r:ℝ)^2 = S / 8 := by rw [hτdef]; field_simp
  have h46 : ∀ i j, 1 ≤ i → i < j → j < r+1 → τ ≤ h i → τ ≤ h j →
      min (h i) (h j) < ∑ v ∈ Finset.Ico (i+1) j, h v := by
    intro i j h1 h2 h3 h4 h5
    by_contra hcon
    rw [not_lt, Finset.Ico_add_one_left_eq_Ioo] at hcon
    exact halt ⟨i, j, h1, h2, by omega, h4, h5, hcon⟩
  obtain ⟨z, hz, hzmax⟩ := Finset.exists_max_image (Finset.Ico 1 (r+1)) h
    ⟨1, by rw [Finset.mem_Ico]; omega⟩
  rw [Finset.mem_Ico] at hz
  refine ⟨z, hz.1, by omega, ?_⟩
  have hbτ : τ ≤ h z := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : S ≤ ∑ v ∈ Finset.Ico 1 (r+1), τ :=
      Finset.sum_le_sum fun t ht => (lt_of_le_of_lt (hzmax t ht) hlt).le
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, show r + 1 - 1 = r by omega] at h1
    have : (r:ℝ) * τ ≤ τ * (r:ℝ)^2 := by nlinarith
    linarith
  have hsplit : S = ∑ v ∈ Finset.Ico 1 z, h v + h z + ∑ v ∈ Finset.Ico (z+1) (r+1), h v := by
    rw [hSdef, ← Finset.sum_Ico_consecutive _ hz.1 hz.2.le,
      Finset.sum_eq_sum_Ico_succ_bot hz.2]; ring
  have hL := claim h τ hτ (z - 1) false true 1 z (Or.inr rfl) (by omega)
    (fun t ht => hh t (by rw [Finset.mem_Ico] at ht ⊢; omega))
    (fun i j h1 h2 h3 => h46 i j h1 h2 (by omega))
    (fun i h1 h2 h3 => ⟨fun hf => absurd hf (by simp), fun _ => by
      have := h46 i z h1 h2 hz.2 h3 hbτ
      rwa [min_eq_left (hzmax i (by rw [Finset.mem_Ico]; omega))] at this⟩)
  have hR := claim h τ hτ (r - z) true false (z+1) (r+1) (Or.inl rfl) (by omega)
    (fun t ht => hh t (by rw [Finset.mem_Ico] at ht ⊢; omega))
    (fun i j h1 h2 h3 => h46 i j (by omega) h2 h3)
    (fun i h1 h2 h3 => ⟨fun _ => by
      have := h46 z i hz.1 (by omega) h2 hbτ h3
      rwa [min_eq_right (hzmax i (by rw [Finset.mem_Ico]; omega))] at this,
      fun hf => absurd hf (by simp)⟩)
  norm_num at hL hR
  have hsum : ((z - 1 : ℕ):ℝ) + ((r - z : ℕ):ℝ) ≤ r := by
    exact_mod_cast (by omega : (z - 1) + (r - z) ≤ r)
  have ha0 : (0:ℝ) ≤ ((z - 1 : ℕ):ℝ) := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ ((r - z : ℕ):ℝ) := Nat.cast_nonneg _
  generalize ((z - 1 : ℕ):ℝ) = a at hL hsum ha0
  generalize ((r - z : ℕ):ℝ) = c at hR hsum hc0
  have hsq : a^2 + c^2 ≤ (r:ℝ)^2 := by nlinarith
  have : τ * (a^2 + c^2) ≤ τ * (r:ℝ)^2 := mul_le_mul_of_nonneg_left hsq hτ
  nlinarith
