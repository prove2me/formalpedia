-- Prove2me | solution 1 for PerishBaseStock.Outdating.sZero_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:51:27.356288+00:00
-- url     : https://prove2.me/submissions/af7ca0f7-3fa1-4227-858a-37d8ea824087

import Definitions.Def_PerishBaseStock_Outdating_Heuristic

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

namespace PBS4Z
open PerishBaseStock.Outdating CappedBaseStock LostSalesOrderUpTo.Asymptotic

theorem cdf_mono (P : DemandLaw) {x y : ℝ} (h : x ≤ y) : cdf P x ≤ cdf P y :=
  measure_mono fun d (hd : (d : ℝ) ≤ x) => le_trans hd h

theorem cdf_neg (P : DemandLaw) {x : ℝ} (h : x < 0) : cdf P x = 0 := by
  have : {d : ℝ≥0 | (d : ℝ) ≤ x} = ∅ := by
    ext d; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    linarith [d.2]
  simp [cdf, this]

theorem lsSet_nonempty (P : DemandLaw) : {x : ℝ | 0 < cdf P x}.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h0 : ∀ n : ℕ, P.law {d : ℝ≥0 | (d : ℝ) ≤ n} = 0 := by
    intro n
    have : (n : ℝ) ∉ {x : ℝ | 0 < cdf P x} := by rw [hne]; simp
    simp only [Set.mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at this
    exact this
  have hU : (Set.univ : Set ℝ≥0) = ⋃ n : ℕ, {d : ℝ≥0 | (d : ℝ) ≤ n} := by
    ext d; simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge (d : ℝ)
    exact ⟨n, hn⟩
  have : P.law Set.univ = 0 := by rw [hU]; exact measure_iUnion_null h0
  simp at this

theorem lsSet_bdd (P : DemandLaw) : BddBelow {x : ℝ | 0 < cdf P x} := by
  refine ⟨0, fun x hx => ?_⟩
  by_contra h
  push_neg at h
  simp only [Set.mem_setOf_eq] at hx
  rw [cdf_neg P h] at hx
  exact lt_irrefl _ hx

theorem lowerSupport_nonneg (P : DemandLaw) : 0 ≤ lowerSupport P :=
  le_csInf (lsSet_nonempty P) fun x hx => by
    by_contra h; push_neg at h
    simp only [Set.mem_setOf_eq] at hx
    rw [cdf_neg P h] at hx
    exact lt_irrefl _ hx

theorem law_lt_lowerSupport (P : DemandLaw) :
    P.law {d : ℝ≥0 | (d : ℝ) < lowerSupport P} = 0 := by
  have hU : {d : ℝ≥0 | (d : ℝ) < lowerSupport P} =
      ⋃ n : ℕ, {d : ℝ≥0 | (d : ℝ) ≤ lowerSupport P - 1 / ((n : ℝ) + 1)} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hU]
  refine measure_iUnion_null fun n => ?_
  have hlt : lowerSupport P - 1 / ((n : ℝ) + 1) < lowerSupport P := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have := notMem_of_lt_csInf hlt (lsSet_bdd P)
  simp only [Set.mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at this
  exact this

theorem cdf_pos (P : DemandLaw) {ε : ℝ} (hε : 0 < ε) : 0 < cdf P (lowerSupport P + ε) := by
  obtain ⟨x, hx, hxl⟩ := exists_lt_of_csInf_lt (lsSet_nonempty P)
    (show lowerSupport P < lowerSupport P + ε by linarith)
  exact lt_of_lt_of_le hx (cdf_mono P hxl.le)

/-- The sum `∑_{i<m} d_i` as a real number. -/
def sumR (m : ℕ) (d : DemandPath) : ℝ := ∑ i ∈ Finset.range m, ((d i : ℝ≥0) : ℝ)

theorem excess_eq (P : DemandLaw) (c : Params) (S : ℝ≥0) :
    excessOverLifetimeDemand P c S =
      ∫ d, max ((S : ℝ) - sumR c.m d) 0 ∂demandPathLaw P := by
  unfold excessOverLifetimeDemand expectedHolding leadTimeLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hm : c.m - 1 + 1 = c.m := Nat.sub_add_cancel c.one_le_m
  rw [hm]
  congr 1
  funext d
  simp [sumR]

theorem integrable_excess (P : DemandLaw) (m : ℕ) (S : ℝ≥0) :
    Integrable (fun d => max ((S : ℝ) - sumR m d) 0) (demandPathLaw P) := by
  have hms : Measurable (sumR m) := by
    unfold sumR
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).coe_nnreal_real
  refine Integrable.of_bound ((measurable_const.sub hms).max measurable_const).aestronglyMeasurable
    (S : ℝ) (ae_of_all _ fun d => ?_)
  have h0 : 0 ≤ sumR m d := Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) S.2

theorem excess_zero_of_le (P : DemandLaw) (c : Params) (S : ℝ≥0)
    (hS : (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P) : excessOverLifetimeDemand P c S = 0 := by
  rw [excess_eq]
  have hae : ∀ᵐ d ∂demandPathLaw P, ∀ i, lowerSupport P ≤ ((d i : ℝ≥0) : ℝ) := by
    rw [ae_all_iff]
    intro i
    have hmap : (demandPathLaw P).map (fun d => d i) = P.law := Measure.infinitePi_map_eval _ i
    have h0 := law_lt_lowerSupport P
    rw [← hmap, Measure.map_apply (measurable_pi_apply i)] at h0
    · rw [ae_iff]
      simp only [not_le]
      exact h0
    · exact measurableSet_lt (by fun_prop) measurable_const
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with d hd
  have : (c.m : ℝ) * lowerSupport P ≤ sumR c.m d := by
    unfold sumR
    calc (c.m : ℝ) * lowerSupport P = ∑ i ∈ Finset.range c.m, lowerSupport P := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hd i
  simp only [Pi.zero_apply]
  exact max_eq_right (by linarith)

theorem excess_pos_of_lt (P : DemandLaw) (c : Params) (S : ℝ≥0)
    (hS : (c.m : ℝ) * lowerSupport P < (S : ℝ)) : 0 < excessOverLifetimeDemand P c S := by
  rw [excess_eq]
  have hmr : (1 : ℝ) ≤ c.m := by exact_mod_cast c.one_le_m
  set L := lowerSupport P
  have hL := lowerSupport_nonneg P
  set ε : ℝ := ((S : ℝ) - c.m * L) / (2 * c.m) with hε
  have hεpos : 0 < ε := by apply div_pos <;> linarith
  set a : ℝ≥0 := ⟨L + ε, by linarith⟩
  set B : Set DemandPath := Set.pi (Finset.range c.m : Set ℕ) (fun _ => Set.Iic a)
  have hB : 0 < demandPathLaw P B := by
    unfold B demandPathLaw
    erw [Measure.infinitePi_pi (μ := fun _ : ℕ => P.law) (fun _ _ => measurableSet_Iic)]
    rw [Finset.prod_const]
    refine ENNReal.pow_pos ?_ _
    have := cdf_pos P hεpos
    unfold cdf at this
    convert this using 2
    ext d
    simp only [Set.mem_Iic, Set.mem_setOf_eq]
    rw [← NNReal.coe_le_coe]
    rfl
  rw [integral_pos_iff_support_of_nonneg (f := fun d => max ((S : ℝ) - sumR c.m d) 0)
    (fun d => le_max_right _ _) (integrable_excess P c.m S)]
  refine lt_of_lt_of_le hB (measure_mono fun d hd => ?_)
  simp only [B, Set.mem_pi, Finset.mem_coe, Finset.mem_range, Set.mem_Iic] at hd
  have hsum : sumR c.m d ≤ c.m * (L + ε) := by
    unfold sumR
    calc ∑ i ∈ Finset.range c.m, ((d i : ℝ≥0) : ℝ) ≤ ∑ i ∈ Finset.range c.m, (L + ε) :=
          Finset.sum_le_sum fun i hi => by
            have := hd i (Finset.mem_range.1 hi)
            exact (NNReal.coe_le_coe.2 this)
      _ = c.m * (L + ε) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hkey : (c.m : ℝ) * (L + ε) < S := by
    have : (c.m : ℝ) * ε = ((S : ℝ) - c.m * L) / 2 := by
      rw [hε]; field_simp
    nlinarith
  simp only [Function.mem_support]
  apply ne_of_gt
  exact lt_max_of_lt_left (by linarith)

end PBS4Z

open PerishBaseStock.Outdating PBS4Z in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) :
    sZero P c = (c.m : ℝ) * lowerSupport P := by
  have hL := lowerSupport_nonneg P
  have hm0 : (0 : ℝ) ≤ c.m := Nat.cast_nonneg _
  have hset : ((fun S : ℝ≥0 => (S : ℝ)) '' {S : ℝ≥0 | excessOverLifetimeDemand P c S = 0}) =
      Set.Icc 0 ((c.m : ℝ) * lowerSupport P) := by
    ext s
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨S, hS, rfl⟩
      refine ⟨S.2, ?_⟩
      by_contra h
      push_neg at h
      have := excess_pos_of_lt P c S h
      linarith
    · rintro ⟨h0, h1⟩
      exact ⟨⟨s, h0⟩, excess_zero_of_le P c ⟨s, h0⟩ h1, rfl⟩
  unfold sZero
  rw [hset, csSup_Icc (by positivity)]
