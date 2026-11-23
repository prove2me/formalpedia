-- Prove2me | solution 1 for ObjectCentric.compositional_iff_contrast_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:14:16.609385+00:00
-- url     : https://prove2.me/submissions/421a8e96-89f5-4bb1-9208-17f8327fdb74

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory
namespace ObjectCentric


theorem compositional_iff_contrast_zero {K M N : ℕ} (f : Lat K M → Obs N)
    (hf : Differentiable ℝ f) :
    IsCompositional f ↔ ∀ z : Lat K M, compContrast f z = 0 := by
  have hl0 : ∀ v : Fin M → ℝ, 0 ≤ l2norm v := fun v => Real.sqrt_nonneg _
  have hlz : ∀ v : Fin M → ℝ, l2norm v = 0 ↔ v = 0 := by
    intro v
    constructor
    · intro h
      rw [l2norm, Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _),
        Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h
      funext i
      exact (pow_eq_zero_iff two_ne_zero).mp (h i (Finset.mem_univ _))
    · intro h; simp [l2norm, h]
  unfold IsCompositional compContrast
  constructor
  · intro h z
    apply Finset.sum_eq_zero; intro n _
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro j hj
    have hkj : k ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    by_cases hk : slotGrad f z n k = 0
    · rw [hk, (hlz 0).mpr rfl, zero_mul]
    · have hn : n ∉ indexSet f z j := fun hn => Set.disjoint_left.mp (h z k j hkj) hk hn
      have hj0 : slotGrad f z n j = 0 := by simpa [indexSet] using hn
      rw [hj0, (hlz 0).mpr rfl, mul_zero]
  · intro h z k j hkj
    rw [Set.disjoint_left]
    intro n hk hj
    have key : ∀ a b : Fin K, a < b → slotGrad f z n a ≠ 0 → slotGrad f z n b ≠ 0 → False := by
      intro a b hab ha hb
      have hpos : 0 < l2norm (slotGrad f z n a) * l2norm (slotGrad f z n b) :=
        mul_pos (lt_of_le_of_ne (hl0 _) (fun e => ha ((hlz _).mp e.symm)))
          (lt_of_le_of_ne (hl0 _) (fun e => hb ((hlz _).mp e.symm)))
      have hle : l2norm (slotGrad f z n a) * l2norm (slotGrad f z n b) ≤
          ∑ n, ∑ k, ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j) :=
        calc _ ≤ ∑ j ∈ Finset.Ioi a, l2norm (slotGrad f z n a) * l2norm (slotGrad f z n j) :=
              Finset.single_le_sum (f := fun j => l2norm (slotGrad f z n a) * l2norm (slotGrad f z n j))
                (fun j _ => mul_nonneg (hl0 _) (hl0 _)) (Finset.mem_Ioi.mpr hab)
          _ ≤ ∑ k, ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j) :=
              Finset.single_le_sum (f := fun k => ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j))
                (fun k _ => Finset.sum_nonneg fun j _ => mul_nonneg (hl0 _) (hl0 _)) (Finset.mem_univ a)
          _ ≤ _ :=
              Finset.single_le_sum (f := fun n => ∑ k, ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j))
                (fun n _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => mul_nonneg (hl0 _) (hl0 _)) (Finset.mem_univ n)
      linarith [h z]
    rcases lt_or_gt_of_ne hkj with hl | hl
    · exact key k j hl hk hj
    · exact key j k hl hj hk


end ObjectCentric

open ObjectCentric in
theorem solution {K M N : ℕ} (f : Lat K M → Obs N)
    (hf : Differentiable ℝ f) :
    IsCompositional f ↔ ∀ z : Lat K M, compContrast f z = 0 := by
  have hl0 : ∀ v : Fin M → ℝ, 0 ≤ l2norm v := fun v => Real.sqrt_nonneg _
  have hlz : ∀ v : Fin M → ℝ, l2norm v = 0 ↔ v = 0 := by
    intro v
    constructor
    · intro h
      rw [l2norm, Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _),
        Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h
      funext i
      exact (pow_eq_zero_iff two_ne_zero).mp (h i (Finset.mem_univ _))
    · intro h; simp [l2norm, h]
  unfold IsCompositional compContrast
  constructor
  · intro h z
    apply Finset.sum_eq_zero; intro n _
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro j hj
    have hkj : k ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    by_cases hk : slotGrad f z n k = 0
    · rw [hk, (hlz 0).mpr rfl, zero_mul]
    · have hn : n ∉ indexSet f z j := fun hn => Set.disjoint_left.mp (h z k j hkj) hk hn
      have hj0 : slotGrad f z n j = 0 := by simpa [indexSet] using hn
      rw [hj0, (hlz 0).mpr rfl, mul_zero]
  · intro h z k j hkj
    rw [Set.disjoint_left]
    intro n hk hj
    have key : ∀ a b : Fin K, a < b → slotGrad f z n a ≠ 0 → slotGrad f z n b ≠ 0 → False := by
      intro a b hab ha hb
      have hpos : 0 < l2norm (slotGrad f z n a) * l2norm (slotGrad f z n b) :=
        mul_pos (lt_of_le_of_ne (hl0 _) (fun e => ha ((hlz _).mp e.symm)))
          (lt_of_le_of_ne (hl0 _) (fun e => hb ((hlz _).mp e.symm)))
      have hle : l2norm (slotGrad f z n a) * l2norm (slotGrad f z n b) ≤
          ∑ n, ∑ k, ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j) :=
        calc _ ≤ ∑ j ∈ Finset.Ioi a, l2norm (slotGrad f z n a) * l2norm (slotGrad f z n j) :=
              Finset.single_le_sum (f := fun j => l2norm (slotGrad f z n a) * l2norm (slotGrad f z n j))
                (fun j _ => mul_nonneg (hl0 _) (hl0 _)) (Finset.mem_Ioi.mpr hab)
          _ ≤ ∑ k, ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j) :=
              Finset.single_le_sum (f := fun k => ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j))
                (fun k _ => Finset.sum_nonneg fun j _ => mul_nonneg (hl0 _) (hl0 _)) (Finset.mem_univ a)
          _ ≤ _ :=
              Finset.single_le_sum (f := fun n => ∑ k, ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j))
                (fun n _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => mul_nonneg (hl0 _) (hl0 _)) (Finset.mem_univ n)
      linarith [h z]
    rcases lt_or_gt_of_ne hkj with hl | hl
    · exact key k j hl hk hj
    · exact key j k hl hj hk

