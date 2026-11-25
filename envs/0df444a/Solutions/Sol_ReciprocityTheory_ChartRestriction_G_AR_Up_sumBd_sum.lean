-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:28.329164+00:00
-- url     : https://prove2.me/submissions/dbf19cf1-d8cf-4131-84ef-7e467fee6612

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_w_le_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_w_le_big
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_prod_le_big
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_count_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {f : ℕ} {s c : ℝ} (hs : 2 * (f : ℝ) * ((p + q : ℕ) : ℝ) ^ 2 < s) (hc : 0 < c) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ),
      (∀ a k, IsUpq (x a k)) →
      (∀ a b, a ≠ b → ∃ k i j,
        c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) →
      ∑' a, ENNReal.ofReal (∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s) ≤ C := by
  classical
  set P : ℝ := ((p + q : ℕ) : ℝ) with hP
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  set K : ℝ := 4 * (P + 1) / c + 3 with hK
  have hK0 : 0 ≤ K := by positivity
  set D : ℕ := f * ((p + q) * ((p + q) * 2)) with hD
  set B : ℝ := 4 * (P + 1) with hB
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hDs : (D : ℝ) < s := by
    have : (D : ℝ) = 2 * (f : ℝ) * P ^ 2 := by rw [hD, hP]; push_cast; ring
    rw [this]; exact hs
  have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg _) hDs.le
  set ρ : ℝ := (4 : ℝ) ^ D / 4 ^ s with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by positivity), ← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hDs
  refine ⟨ENNReal.ofReal (K ^ D * B ^ s) * ∑' j : ℕ, ENNReal.ofReal (ρ ^ j), ?_, ?_⟩
  · have hg : ∑' j : ℕ, ENNReal.ofReal (ρ ^ j) = (1 - ENNReal.ofReal ρ)⁻¹ := by
      rw [← ENNReal.tsum_geometric]
      exact tsum_congr fun j => ENNReal.ofReal_pow hρ0 j
    rw [hg]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    rw [ENNReal.inv_lt_top]
    exact tsub_pos_of_lt (ENNReal.ofReal_lt_one.mpr hρ1)
  intro ι x hU hsep
  set Bs : ℕ → Set ι := fun m => {a | ∀ k i j, ‖x a k i j‖ ≤ (2 : ℝ) ^ m} with hBs
  set g : ι → ℝ≥0∞ := fun a => ENNReal.ofReal (∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s)
    with hgdef
  have hex : ∀ a, ∃ m, a ∈ Bs m := by
    intro a
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (∑ k, ∑ i, ∑ j, ‖x a k i j‖) (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, fun k i j => le_trans ?_ hm.le⟩
    calc ‖x a k i j‖ ≤ ∑ j', ‖x a k i j'‖ :=
          Finset.single_le_sum (f := fun j' => ‖x a k i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖x a k i' j'‖ :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖x a k i' j'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ k', ∑ i', ∑ j', ‖x a k' i' j'‖ :=
          Finset.single_le_sum (f := fun k' => ∑ i', ∑ j', ‖x a k' i' j'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ k)
  have hw0 : ∀ a k, 0 ≤ (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s := fun a k =>
    (sumBd_w_le_one (hU a k) hs0).1
  have hw1 : ∀ a k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s ≤ 1 := fun a k =>
    (sumBd_w_le_one (hU a k) hs0).2
  have hpt : ∀ a, g a ≤ ∑' m : ℕ, (Bs m).indicator (fun _ => ENNReal.ofReal ((B / 4 ^ m) ^ s)) a := by
    intro a
    let m0 := Nat.find (hex a)
    have hm0 : a ∈ Bs m0 := Nat.find_spec (hex a)
    refine le_trans ?_ (ENNReal.le_tsum m0)
    rw [Set.indicator_of_mem hm0]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases Nat.eq_zero_or_pos m0 with h0 | hpos
    · rw [h0, pow_zero, div_one]
      calc ∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s ≤ 1 :=
            Finset.prod_le_one (fun k _ => hw0 a k) (fun k _ => hw1 a k)
        _ ≤ B ^ s := Real.one_le_rpow hB1 hs0
    · obtain ⟨m, hm⟩ : ∃ m, m0 = m + 1 := ⟨m0 - 1, by omega⟩
      have hnot : a ∉ Bs m := Nat.find_min (hex a) (by omega)
      simp only [hBs, Set.mem_setOf_eq, not_forall, not_le] at hnot
      obtain ⟨k, i, j, hkij⟩ := hnot
      have hbig := sumBd_w_le_big (hU a k) hs0 (by positivity : (0 : ℝ) < 2 ^ m) hkij
      have hfac : (P + 1) / ((2 : ℝ) ^ m) ^ 2 = B / 4 ^ m0 := by
        have h4 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [h4, hm, hB, pow_succ]
        field_simp
      rw [hfac] at hbig
      exact sumBd_prod_le_big _ (hw0 a) (hw1 a) k hbig
  calc ∑' a, ENNReal.ofReal (∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s)
      = ∑' a, g a := rfl
    _ ≤ ∑' a, ∑' m : ℕ, (Bs m).indicator (fun _ => ENNReal.ofReal ((B / 4 ^ m) ^ s)) a :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' m : ℕ, ∑' a, (Bs m).indicator (fun _ => ENNReal.ofReal ((B / 4 ^ m) ^ s)) a :=
        ENNReal.tsum_comm
    _ = ∑' m : ℕ, (Bs m).encard * ENNReal.ofReal ((B / 4 ^ m) ^ s) := by
        refine tsum_congr fun m => ?_
        rw [← tsum_subtype (Bs m) (fun _ => ENNReal.ofReal ((B / 4 ^ m) ^ s)), ENNReal.tsum_set_const]
    _ ≤ ∑' m : ℕ, ENNReal.ofReal ((K * ((2 : ℝ) ^ m) ^ 2) ^ D) * ENNReal.ofReal ((B / 4 ^ m) ^ s) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        gcongr
        exact sumBd_count_real x hU hc hsep (R := (2 : ℝ) ^ m) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    _ = ∑' m : ℕ, ENNReal.ofReal (K ^ D * B ^ s) * ENNReal.ofReal (ρ ^ m) := by
        refine tsum_congr fun m => ?_
        rw [← ENNReal.ofReal_mul (by positivity), sumBd_id K B s D m (by linarith),
          ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (K ^ D * B ^ s) * ∑' j : ℕ, ENNReal.ofReal (ρ ^ j) := ENNReal.tsum_mul_left
end ReciprocityTheory.ChartRestriction.G.AR.Up
