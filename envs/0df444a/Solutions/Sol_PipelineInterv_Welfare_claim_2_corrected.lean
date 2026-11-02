-- Prove2me | solution 1 for PipelineInterv.Welfare.claim_2_corrected
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:58:57.178487+00:00
-- url     : https://prove2.me/submissions/35166564-131c-4fa5-a4b9-60be18b01601

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model
open Matrix

open PipelineInterv.Welfare in
theorem solution {w : ℕ} (hw : 1 ≤ w) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset (Fin w → ℝ), IsEpsNet ε S ∧
      S.card ≤ (⌈2 * (w : ℝ) / ε⌉₊ + 1) ^ (w - 1) := by
  classical
  set m : ℕ := ⌈2 * (w : ℝ) / ε⌉₊ with hm
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw
  have hm1 : 2 * (w : ℝ) / ε ≤ m := Nat.le_ceil _
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm1
  set last : Fin w := ⟨w - 1, by omega⟩
  set E := Finset.univ.erase last
  have hEcard : E.card = w - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  let pt : (Fin w → ℕ) → (Fin w → ℝ) := fun g i =>
    if i = last then 1 - ∑ j ∈ E, (g j : ℝ) / m else (g i : ℝ) / m
  let G := Fintype.piFinset (fun i : Fin w => if i = last then ({0} : Finset ℕ) else Finset.range (m + 1))
  refine ⟨(G.image pt).filter IsDist, ⟨fun D hD => (Finset.mem_filter.1 hD).2, ?_⟩, ?_⟩
  · intro D hD
    have hDle : ∀ i, D i ≤ 1 := fun i => by
      rw [← hD.2]; exact Finset.single_le_sum (fun j _ => hD.1 j) (Finset.mem_univ i)
    let g : Fin w → ℕ := fun i => if i = last then 0 else ⌊(m : ℝ) * D i⌋₊
    have hgE : ∀ i ∈ E, (g i : ℝ) / m ≤ D i ∧ D i - 1 / m < (g i : ℝ) / m := by
      intro i hi
      have hil : i ≠ last := Finset.ne_of_mem_erase hi
      simp only [g, if_neg hil]
      have h0 : 0 ≤ (m : ℝ) * D i := mul_nonneg hmpos.le (hD.1 i)
      constructor
      · rw [div_le_iff₀ hmpos]; linarith [Nat.floor_le h0]
      · rw [lt_div_iff₀ hmpos]
        have := Nat.lt_floor_add_one ((m : ℝ) * D i)
        have e : (D i - 1 / m) * m = m * D i - 1 := by field_simp
        rw [e]; linarith
    have hsumD : D last = 1 - ∑ j ∈ E, D j := by
      rw [← hD.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ last)]; ring
    have hsumle : ∑ j ∈ E, (g j : ℝ) / m ≤ ∑ j ∈ E, D j :=
      Finset.sum_le_sum fun j hj => (hgE j hj).1
    have hptE : ∀ i ∈ E, pt g i = (g i : ℝ) / m := fun i hi => by
      simp only [pt, if_neg (Finset.ne_of_mem_erase hi)]
    have hptl : pt g last = 1 - ∑ j ∈ E, (g j : ℝ) / m := by simp [pt]
    refine ⟨pt g, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨g, ?_, rfl⟩, ?_⟩, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      by_cases hil : i = last
      · simp [g, hil]
      · simp only [g, if_neg hil, Finset.mem_range]
        have : ⌊(m : ℝ) * D i⌋₊ ≤ m := by
          apply Nat.floor_le_of_le
          nlinarith [hDle i]
        omega
    · refine ⟨fun i => ?_, ?_⟩
      · by_cases hil : i = last
        · rw [hil, hptl]
          have := hD.1 last
          linarith
        · rw [hptE i (Finset.mem_erase.2 ⟨hil, Finset.mem_univ _⟩)]; positivity
      · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ last), hptl,
          Finset.sum_congr rfl hptE]
        ring
    · unfold l1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ last)]
      simp only [Pi.sub_apply]
      rw [hptl]
      have h1 : |D last - (1 - ∑ j ∈ E, (g j : ℝ) / m)| = ∑ j ∈ E, (D j - (g j : ℝ) / m) := by
        rw [hsumD, Finset.sum_sub_distrib, abs_of_nonpos (by linarith)]
        ring
      have h2 : ∑ j ∈ Finset.univ.erase last, |D j - pt g j| = ∑ j ∈ E, (D j - (g j : ℝ) / m) :=
        Finset.sum_congr rfl fun j hj => by
          rw [hptE j hj]; exact abs_of_nonneg (by linarith [(hgE j hj).1])
      rw [h1, h2]
      have h3 : ∑ j ∈ E, (D j - (g j : ℝ) / m) ≤ ∑ j ∈ E, (1 / (m : ℝ)) :=
        Finset.sum_le_sum fun j hj => by linarith [(hgE j hj).2]
      rw [Finset.sum_const, hEcard, nsmul_eq_mul] at h3
      have h4 : ((w - 1 : ℕ) : ℝ) ≤ w := by exact_mod_cast Nat.sub_le w 1
      have h5 : 2 * (w : ℝ) * (1 / m) ≤ ε := by
        rw [mul_one_div, div_le_iff₀ hmpos]
        rw [div_le_iff₀ hε] at hm1; linarith
      have h6 : ((w - 1 : ℕ) : ℝ) * (1 / m) ≤ w * (1 / m) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      linarith
  · calc ((G.image pt).filter IsDist).card ≤ (G.image pt).card := Finset.card_filter_le _ _
      _ ≤ G.card := Finset.card_image_le
      _ = (m + 1) ^ (w - 1) := by
        rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ last)]
        rw [if_pos rfl, Finset.card_singleton, one_mul]
        rw [Finset.prod_congr rfl (fun i hi => by
          rw [if_neg (Finset.ne_of_mem_erase hi), Finset.card_range])]
        rw [Finset.prod_const]
        change (m + 1) ^ E.card = _
        rw [hEcard]
