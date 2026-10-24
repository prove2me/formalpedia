-- Prove2me | solution 1 for PermInvConvex.Sparsity.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:04:40.914203+00:00
-- url     : https://prove2.me/submissions/790f0b8b-273b-4084-b36d-077793f99c9d

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

open PermInvConvex.Sparsity

theorem solution {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) (hx : card x ≤ K) :
    normC ns K x = ns x := by
  have hzero : ns 0 = 0 := (hns.eq_zero_iff 0).mpr rfl
  by_cases hxzero : x = 0
  · subst x
    simp only [normC, gauge_zero, hzero]
  have hnonneg : 0 ≤ ns x := by
    have hneg : ns ((-1 : ℝ) • x) = ns x := by
      rw [hns.smul]
      norm_num
    have hadd := hns.add_le x ((-1 : ℝ) • x)
    have hcancel : x + (-1 : ℝ) • x = 0 := by simp
    rw [hcancel, hzero, hneg] at hadd
    linarith
  have hpos : 0 < ns x := lt_of_le_of_ne hnonneg (by
    intro h
    exact hxzero ((hns.eq_zero_iff x).mp h.symm))
  have hnormalized : ns ((ns x)⁻¹ • x) = 1 := by
    rw [hns.smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
  have hcard : card ((ns x)⁻¹ • x) ≤ card x := by
    classical
    unfold card
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply, smul_eq_mul]
      at hi ⊢
    intro h
    exact hi (by rw [h, mul_zero])
  have hmem : (ns x)⁻¹ • x ∈ convexHull ℝ (NK ns K) :=
    subset_convexHull ℝ _ ⟨hnormalized.le, hcard.trans hx⟩
  have hconv : Convex ℝ {z : Fin n → ℝ | ns z ≤ 1} := by
    intro u hu v hv a b ha hb hab
    change ns (a • u + b • v) ≤ 1
    calc
      ns (a • u + b • v) ≤ ns (a • u) + ns (b • v) := hns.add_le _ _
      _ = a * ns u + b * ns v := by
        rw [hns.smul, hns.smul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
      _ = 1 := by simpa only [mul_one] using hab
  have hsubset : convexHull ℝ (NK ns K) ⊆ {z : Fin n → ℝ | ns z ≤ 1} :=
    convexHull_min (fun _ hz => hz.1) hconv
  rw [normC, gauge_def']
  apply le_antisymm
  · exact csInf_le ⟨0, fun r hr => hr.1.le⟩ ⟨hpos, hmem⟩
  · refine le_csInf ⟨ns x, hpos, hmem⟩ ?_
    intro r hr
    have hrpos : 0 < r := hr.1
    have hbound := hsubset hr.2
    change ns (r⁻¹ • x) ≤ 1 at hbound
    rw [hns.smul, abs_of_pos (inv_pos.mpr hrpos)] at hbound
    have hscaled := mul_le_mul_of_nonneg_left hbound hrpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hrpos.ne', one_mul, mul_one] using hscaled
