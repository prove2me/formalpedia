-- Prove2me | solution 1 for SinkhornHall.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:47:04.814096+00:00
-- url     : https://prove2.me/submissions/57d2fc3e-aad0-4634-b37b-d61db4550d3c

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset SinkhornHall

private noncomputable def pinskerD1 (u : ℝ) : ℝ :=
  Real.log u - 3 / 2 + (27 / 2 : ℝ) / (u + 2) ^ 2

private noncomputable def pinskerD2 (u : ℝ) : ℝ :=
  1 / u - 27 / (u + 2) ^ 3

private lemma hasDerivAt_pinskerD1 {u : ℝ} (hu : 0 < u) :
    HasDerivAt pinskerD1 (pinskerD2 u) u := by
  have hu0 : u ≠ 0 := hu.ne'
  have h2 : u + 2 ≠ 0 := by linarith
  have hlog : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu0
  have hlin : HasDerivAt (fun x : ℝ => x + 2) 1 u := by
    simpa using (hasDerivAt_id' u).add_const (2 : ℝ)
  have hsq : HasDerivAt (fun x : ℝ => (x + 2) ^ 2) ((2 : ℕ) * (u + 2) ^ (2 - 1) * 1) u :=
    hlin.fun_pow 2
  have hdiv : HasDerivAt (fun x : ℝ => (27 / 2 : ℝ) / (x + 2) ^ 2)
      ((0 * (u + 2) ^ 2 - (27 / 2 : ℝ) * ((2 : ℕ) * (u + 2) ^ (2 - 1) * 1)) /
        ((u + 2) ^ 2) ^ 2) u :=
    (hasDerivAt_const u (27 / 2 : ℝ)).fun_div hsq (pow_ne_zero 2 h2)
  have hcomb : HasDerivAt pinskerD1
      (u⁻¹ + (0 * (u + 2) ^ 2 - (27 / 2 : ℝ) * ((2 : ℕ) * (u + 2) ^ (2 - 1) * 1)) /
        ((u + 2) ^ 2) ^ 2) u :=
    (hlog.sub_const (3 / 2 : ℝ)).fun_add hdiv
  refine hcomb.congr_deriv ?_
  unfold pinskerD2
  norm_num
  field_simp
  ring

private lemma pinskerD2_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ pinskerD2 u := by
  have hu0 : u ≠ 0 := hu.ne'
  have h2 : u + 2 ≠ 0 := by linarith
  have heq : pinskerD2 u = (u - 1) ^ 2 * (u + 8) / (u * (u + 2) ^ 3) := by
    unfold pinskerD2
    field_simp [hu0, h2]
    ring
  rw [heq]
  positivity

private lemma pinskerD1_mono : MonotoneOn pinskerD1 (Set.Ioi 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := pinskerD2) (convex_Ioi 0)
    (fun u hu => (hasDerivAt_pinskerD1 hu).continuousAt.continuousWithinAt) ?_ ?_
  · rw [interior_Ioi]
    intro u hu
    exact (hasDerivAt_pinskerD1 hu).hasDerivWithinAt
  · rw [interior_Ioi]
    intro u hu
    exact pinskerD2_nonneg hu

private lemma pinskerD1_one : pinskerD1 1 = 0 := by
  unfold pinskerD1
  rw [Real.log_one]
  norm_num

private noncomputable def pinskerG (u : ℝ) : ℝ :=
  InformationTheory.klFun u - ((3 / 2 : ℝ) * u - 6 + (27 / 2 : ℝ) / (u + 2))

private lemma hasDerivAt_pinskerG {u : ℝ} (hu : 0 < u) :
    HasDerivAt pinskerG (pinskerD1 u) u := by
  have h2 : u + 2 ≠ 0 := by linarith
  have hkl : HasDerivAt InformationTheory.klFun (Real.log u) u :=
    InformationTheory.hasDerivAt_klFun hu.ne'
  have hlin : HasDerivAt (fun x : ℝ => x + 2) 1 u := by
    simpa using (hasDerivAt_id' u).add_const (2 : ℝ)
  have hdiv1 : HasDerivAt (fun x : ℝ => (27 / 2 : ℝ) / (x + 2))
      ((0 * (u + 2) - (27 / 2 : ℝ) * 1) / (u + 2) ^ 2) u :=
    (hasDerivAt_const u (27 / 2 : ℝ)).fun_div hlin h2
  have hpart1 : HasDerivAt (fun x : ℝ => (3 / 2 : ℝ) * x - 6) ((3 / 2 : ℝ) * 1) u :=
    ((hasDerivAt_id' u).const_mul (3 / 2 : ℝ)).sub_const 6
  have hsub : HasDerivAt pinskerG
      (Real.log u - ((3 / 2 : ℝ) * 1 + (0 * (u + 2) - (27 / 2 : ℝ) * 1) / (u + 2) ^ 2)) u :=
    hkl.fun_sub (hpart1.fun_add hdiv1)
  refine hsub.congr_deriv ?_
  unfold pinskerD1
  field_simp
  ring

private lemma pinskerG_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ pinskerG u := by
  have hg1 : pinskerG 1 = 0 := by
    unfold pinskerG InformationTheory.klFun
    rw [Real.log_one]
    norm_num
  rcases le_total 1 u with h1u | hu1
  · have hmono : MonotoneOn pinskerG (Set.Ici 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := pinskerD1) (convex_Ici 1)
        (fun x (hx : 1 ≤ x) =>
          (hasDerivAt_pinskerG (lt_of_lt_of_le zero_lt_one hx)).continuousAt.continuousWithinAt)
        ?_ ?_
      · rw [interior_Ici]
        intro x (hx : 1 < x)
        exact (hasDerivAt_pinskerG (zero_lt_one.trans hx)).hasDerivWithinAt
      · rw [interior_Ici]
        intro x (hx : 1 < x)
        rw [← pinskerD1_one]
        exact pinskerD1_mono (Set.mem_Ioi.mpr zero_lt_one)
          (Set.mem_Ioi.mpr (zero_lt_one.trans hx)) hx.le
    have := hmono (le_rfl : (1 : ℝ) ≤ 1) h1u h1u
    rwa [hg1] at this
  · have hanti : AntitoneOn pinskerG (Set.Ioc 0 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := pinskerD1) (convex_Ioc 0 1)
        (fun x hx => (hasDerivAt_pinskerG hx.1).continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Ioc]
        intro x hx
        exact (hasDerivAt_pinskerG hx.1).hasDerivWithinAt
      · rw [interior_Ioc]
        intro x hx
        rw [← pinskerD1_one]
        exact pinskerD1_mono (Set.mem_Ioi.mpr hx.1) (Set.mem_Ioi.mpr zero_lt_one) hx.2.le
    have := hanti ⟨hu, hu1⟩ ⟨zero_lt_one, le_rfl⟩ hu1
    rwa [hg1] at this

private lemma pinsker_scalar {u : ℝ} (hu : 0 ≤ u) :
    3 * (u - 1) ^ 2 ≤ (2 * u + 4) * (u * Real.log u - u + 1) := by
  rcases eq_or_lt_of_le hu with rfl | hu_pos
  · norm_num
  · have hpos4 : 0 < 2 * u + 4 := by linarith
    have hpos4_ne : 2 * u + 4 ≠ 0 := hpos4.ne'
    have h2 : u + 2 ≠ 0 := by linarith
    have hg := pinskerG_nonneg hu_pos
    have hpf : (3 / 2 : ℝ) * u - 6 + (27 / 2 : ℝ) / (u + 2) =
        3 * (u - 1) ^ 2 / (2 * u + 4) := by
      field_simp [hpos4_ne, h2]
      ring
    unfold pinskerG InformationTheory.klFun at hg
    rw [hpf, sub_nonneg, div_le_iff₀ hpos4] at hg
    linarith

private lemma pinsker_term {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b = 0 → a = 0) :
    3 * (a - b) ^ 2 ≤ (2 * a + 4 * b) * (a * Real.log (a / b) - a + b) ∧
      0 ≤ a * Real.log (a / b) - a + b := by
  by_cases hb0 : b = 0
  · have ha0 := hba hb0
    simp [hb0, ha0]
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hsc := pinsker_scalar (div_nonneg ha hb_pos.le)
    have hm := mul_le_mul_of_nonneg_left hsc (sq_nonneg b)
    have hL : b ^ 2 * (3 * (a / b - 1) ^ 2) = 3 * (a - b) ^ 2 := by
      field_simp [hb0]
    have hR : b ^ 2 * ((2 * (a / b) + 4) * (a / b * Real.log (a / b) - a / b + 1)) =
        (2 * a + 4 * b) * (a * Real.log (a / b) - a + b) := by
      field_simp [hb0]
    rw [hL, hR] at hm
    have hkl : 0 ≤ b * InformationTheory.klFun (a / b) :=
      mul_nonneg hb_pos.le (InformationTheory.klFun_nonneg (div_nonneg ha hb_pos.le))
    have hkl_eq : b * InformationTheory.klFun (a / b) = a * Real.log (a / b) - a + b := by
      unfold InformationTheory.klFun
      field_simp [hb0]
      ring
    rw [hkl_eq] at hkl
    exact ⟨hm, hkl⟩

theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, p i = ∑ i, q i) :
    (((∑ i, |p i - q i|) ^ 2 / (2 * ∑ i, p i) : ℝ) : EReal) ≤ klDiv p q := by
  by_cases htop : ∃ i, q i = 0 ∧ 0 < p i
  · rw [klDiv, if_pos htop]
    exact le_top
  · rw [klDiv, if_neg htop, EReal.coe_le_coe_iff]
    have hqp : ∀ i, q i = 0 → p i = 0 := by
      intro i hq0
      by_contra hp0
      exact htop ⟨i, hq0, lt_of_le_of_ne (hp i) (Ne.symm hp0)⟩
    by_cases hS : ∑ i, p i = 0
    · have hp_zero : ∀ i, p i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp j)).mp hS i (Finset.mem_univ i)
      simp [hp_zero]
    · have hS_nonneg : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => hp i)
      have hS_pos : 0 < ∑ i, p i := lt_of_le_of_ne hS_nonneg (Ne.symm hS)
      let w : ι → ℝ := fun i => 2 * p i + 4 * q i
      let d : ι → ℝ := fun i => p i * Real.log (p i / q i) - p i + q i
      have hw_nonneg : ∀ i, 0 ≤ w i := fun i => by dsimp [w]; linarith [hp i, hq i]
      have hd_nonneg : ∀ i, 0 ≤ d i := fun i => (pinsker_term (hp i) (hq i) (hqp i)).2
      have hpt : ∀ i, Real.sqrt 3 * |p i - q i| ≤ Real.sqrt (w i) * Real.sqrt (d i) := by
        intro i
        have h3 := (pinsker_term (hp i) (hq i) (hqp i)).1
        have hsq := Real.sqrt_le_sqrt h3
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq_eq_abs,
          Real.sqrt_mul (hw_nonneg i)] at hsq
        exact hsq
      have hsum_le : Real.sqrt 3 * ∑ i, |p i - q i| ≤ ∑ i, Real.sqrt (w i) * Real.sqrt (d i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => hpt i)
      have h0L : 0 ≤ Real.sqrt 3 * ∑ i, |p i - q i| :=
        mul_nonneg (Real.sqrt_nonneg 3) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
      have hsq_le : 3 * (∑ i, |p i - q i|) ^ 2 ≤
          (∑ i, Real.sqrt (w i) * Real.sqrt (d i)) ^ 2 := by
        have hmul := mul_self_le_mul_self h0L hsum_le
        calc 3 * (∑ i, |p i - q i|) ^ 2
            = (Real.sqrt 3) ^ 2 * (∑ i, |p i - q i|) ^ 2 := by
              rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
          _ = (Real.sqrt 3 * ∑ i, |p i - q i|) * (Real.sqrt 3 * ∑ i, |p i - q i|) := by ring
          _ ≤ _ := hmul
          _ = (∑ i, Real.sqrt (w i) * Real.sqrt (d i)) ^ 2 := (sq _).symm
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (d i))
      have hw_sum : ∑ i, (Real.sqrt (w i)) ^ 2 = 6 * ∑ i, p i := by
        have : ∑ i, (Real.sqrt (w i)) ^ 2 = ∑ i, (2 * p i + 4 * q i) := by
          refine Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hw_nonneg i))
        rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hsum]
        ring
      have hd_sum : ∑ i, (Real.sqrt (d i)) ^ 2 = ∑ i, p i * Real.log (p i / q i) := by
        have : ∑ i, (Real.sqrt (d i)) ^ 2 =
            ∑ i, (p i * Real.log (p i / q i) - p i + q i) := by
          refine Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hd_nonneg i))
        rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum]
        ring
      rw [hw_sum, hd_sum] at hcs
      have hmain : 3 * (∑ i, |p i - q i|) ^ 2 ≤
          (6 * ∑ i, p i) * ∑ i, p i * Real.log (p i / q i) := hsq_le.trans hcs
      rw [div_le_iff₀ (by linarith)]
      linarith
