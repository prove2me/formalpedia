-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.two_moment_unit_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:08:39.04732+00:00
-- url     : https://prove2.me/submissions/2cd959ec-d13b-4272-ba1b-e80146e03bd4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators ENNReal

/-- For nonnegative `s`, `(T² − Σ s²)² ≥ 2((Σ s²)² − Σ s⁴)` where `T = Σ s`. -/
lemma X7_two_moment_key {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, 0 ≤ s i) :
    0 ≤ (∑ i, s i) ^ 2 - ∑ i, s i ^ 2 ∧
    2 * ((∑ i, s i ^ 2) ^ 2 - ∑ i, s i ^ 4) ≤ ((∑ i, s i) ^ 2 - ∑ i, s i ^ 2) ^ 2 := by
  classical
  set a : Fin N × Fin N → ℝ := fun x => if x.1 = x.2 then 0 else s x.1 * s x.2 with ha
  have ha0 : ∀ x, 0 ≤ a x := by
    intro x; simp only [ha]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hs _) (hs _)
  have hsym : ∀ x, a x.swap = a x := by
    intro x; simp only [ha, Prod.fst_swap, Prod.snd_swap, eq_comm (a := x.2), mul_comm]
  have hdiag : ∀ f : Fin N → Fin N → ℝ,
      ∑ x : Fin N × Fin N, (if x.1 = x.2 then 0 else f x.1 x.2) =
        ∑ x : Fin N × Fin N, f x.1 x.2 - ∑ i, f i i := by
    intro f
    have : ∀ x : Fin N × Fin N, (if x.1 = x.2 then 0 else f x.1 x.2) =
        f x.1 x.2 - (if x.1 = x.2 then f x.1 x.2 else 0) := by
      intro x; split_ifs <;> simp_all
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_sub_distrib]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  have hsum : ∑ x, a x = (∑ i, s i) ^ 2 - ∑ i, s i ^ 2 := by
    simp only [ha]
    rw [hdiag (fun i j => s i * s j), Fintype.sum_prod_type, sq, Finset.sum_mul_sum]
    simp [sq]
  have hsq : ∑ x, a x ^ 2 = (∑ i, s i ^ 2) ^ 2 - ∑ i, s i ^ 4 := by
    have : ∀ x, a x ^ 2 = if x.1 = x.2 then 0 else s x.1 ^ 2 * s x.2 ^ 2 := by
      intro x; simp only [ha]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun x _ => this x), hdiag (fun i j => s i ^ 2 * s j ^ 2),
      Fintype.sum_prod_type, sq (∑ i, s i ^ 2), Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  refine ⟨hsum ▸ Finset.sum_nonneg (fun x _ => ha0 x), ?_⟩
  rw [← hsum, ← hsq]
  have hpt : ∀ x, a x * (a x + a x.swap) ≤ a x * ∑ y, a y := by
    intro x
    by_cases hx : x.1 = x.2
    · have : a x = 0 := by simp [ha, hx]
      simp [this]
    · apply mul_le_mul_of_nonneg_left _ (ha0 x)
      have hne : x ≠ x.swap := by
        intro h; apply hx; have := congrArg Prod.fst h; simpa using this
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun y _ _ => ha0 y)
  have h1 : ∑ x, a x * (a x + a x.swap) = 2 * ∑ x, a x ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hsym]; ring
  calc 2 * ∑ x, a x ^ 2 = ∑ x, a x * (a x + a x.swap) := h1.symm
    _ ≤ ∑ x, a x * ∑ y, a y := Finset.sum_le_sum (fun x _ => hpt x)
    _ = (∑ x, a x) ^ 2 := by rw [← Finset.sum_mul, sq]

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (r1 r2 : ℝ) (hlo : 1/2≤r1) (hhi : r1≤1) (h2 : 0≤r2)
    (hupper : r2≤r1^2) :
    alpha ![r1,r2] ≤ 1 ↔ 2*r2-r1^2 ≥ 2*r1-1 := by
  constructor
  · intro hα
    by_contra hcon
    push_neg at hcon
    set D := 2 * (r1 ^ 2 - r2) with hD
    have hD0 : 0 ≤ D := by rw [hD]; linarith
    have hsD : 1 - r1 < Real.sqrt D := by
      rw [Real.lt_sqrt (by linarith)]; rw [hD]; nlinarith
    set m := Real.sqrt (r1 + Real.sqrt D)
    have hm : 1 < m := by
      rw [Real.lt_sqrt (by norm_num)]; linarith
    have hlow : ENNReal.ofReal m ≤ alpha ![r1, r2] := by
      apply le_sInf
      rintro v ⟨N, s, ⟨hs, hmom⟩, rfl⟩
      apply ENNReal.ofReal_le_ofReal
      have h0 : ∀ i, 0 ≤ s i := fun i => (hs i).1
      have hm1 : ∑ i, s i ^ 2 = r1 := by simpa using hmom 0
      have hm2 : ∑ i, s i ^ 4 = r2 := by simpa using hmom 1
      obtain ⟨hP0, hP⟩ := X7_two_moment_key s h0
      rw [hm1] at hP0; rw [hm1, hm2] at hP
      have hT : 0 ≤ ∑ i, s i := Finset.sum_nonneg (fun i _ => h0 i)
      have hPD : Real.sqrt D ≤ (∑ i, s i) ^ 2 - r1 := by
        rw [Real.sqrt_le_left hP0]; rw [hD]; linarith
      rw [Real.sqrt_le_left hT]; linarith
    have : (1 : ℝ≥0∞) < ENNReal.ofReal m := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hm
    exact absurd (lt_of_lt_of_le this (hlow.trans hα)) (lt_irrefl _)
  · intro h
    set p := Real.sqrt ((r1 ^ 2 - r2) / 2) with hp
    have hp0 : 0 ≤ p := Real.sqrt_nonneg _
    have hpsq : p ^ 2 = (r1 ^ 2 - r2) / 2 := Real.sq_sqrt (by linarith)
    have hq0 : 0 ≤ r1 + 2 * p := by linarith
    set q := Real.sqrt (r1 + 2 * p) with hq
    have hqsq : q ^ 2 = r1 + 2 * p := Real.sq_sqrt hq0
    have hqnn : 0 ≤ q := Real.sqrt_nonneg _
    have h2p : 2 * p ≤ 1 - r1 := by
      by_contra hc; push_neg at hc
      nlinarith [mul_self_lt_mul_self (by linarith : (0:ℝ) ≤ 1 - r1) hc]
    have hq1 : q ≤ 1 := by rw [hq, Real.sqrt_le_one]; linarith
    have h2pr : 2 * p ≤ r1 := by
      by_contra hc; push_neg at hc
      nlinarith [mul_self_lt_mul_self (by linarith : (0:ℝ) ≤ r1) hc]
    have hdisc : 0 ≤ q ^ 2 - 4 * p := by rw [hqsq]; linarith
    set w := Real.sqrt (q ^ 2 - 4 * p) with hw
    have hwsq : w ^ 2 = q ^ 2 - 4 * p := Real.sq_sqrt hdisc
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hwq : w ≤ q := by
      rw [hw, Real.sqrt_le_left hqnn]; linarith
    let s : Fin 2 → ℝ := ![(q + w) / 2, (q - w) / 2]
    have hab : (q + w) / 2 * ((q - w) / 2) = p := by nlinarith
    have hs2 : ((q + w) / 2) ^ 2 + ((q - w) / 2) ^ 2 = r1 := by nlinarith
    have hfeas : discreteFeasible ![r1, r2] s := by
      refine ⟨?_, ?_⟩
      · intro i; fin_cases i
        · simp [s]; constructor <;> linarith
        · simp [s]; constructor <;> linarith
      · intro k; fin_cases k
        · simp [s, Fin.sum_univ_two]; linarith
        · simp [s, Fin.sum_univ_two]
          have : ((q + w) / 2) ^ 4 + ((q - w) / 2) ^ 4 =
              (((q + w) / 2) ^ 2 + ((q - w) / 2) ^ 2) ^ 2 -
                2 * ((q + w) / 2 * ((q - w) / 2)) ^ 2 := by ring
          rw [this, hs2, hab, hpsq]; ring
    calc alpha ![r1, r2] ≤ ENNReal.ofReal (∑ i, s i) := sInf_le ⟨2, s, hfeas, rfl⟩
      _ ≤ 1 := by
        rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
        simp [s, Fin.sum_univ_two]; linarith
