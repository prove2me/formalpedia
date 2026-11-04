-- Prove2me | solution 1 for PerishBaseStock.Outdating.eq_EC16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:52:29.798205+00:00
-- url     : https://prove2.me/submissions/0f844ae5-4897-485f-9dfe-a5179beb281d

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

namespace PBS4H
open LostSalesOrderUpTo.Asymptotic CappedBaseStock

theorem meas_sum (k : ℕ) :
    Measurable (fun d : DemandPath => ∑ i ∈ Finset.range (k + 1), d i) := by fun_prop

instance isProb_lead (P : DemandLaw) (k : ℕ) : IsProbabilityMeasure (leadTimeLaw P k) :=
  Measure.isProbabilityMeasure_map (meas_sum k).aemeasurable

theorem coord_integrable (P : DemandLaw) (i : ℕ) :
    Integrable (fun d : DemandPath => ((d i : ℝ≥0) : ℝ)) (demandPathLaw P) := by
  have h : (demandPathLaw P).map (fun d => d i) = P.law :=
    Measure.infinitePi_map_eval _ i
  have hf := P.finiteMean
  rw [← h] at hf
  exact (integrable_map_measure (by fun_prop) (measurable_pi_apply i).aemeasurable).1 hf

theorem lead_integrable (P : DemandLaw) (k : ℕ) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (leadTimeLaw P k) := by
  unfold leadTimeLaw
  refine (integrable_map_measure (by fun_prop) (meas_sum k).aemeasurable).2 ?_
  have : ((fun x : ℝ≥0 => (x : ℝ)) ∘ fun d : DemandPath => ∑ i ∈ Finset.range (k + 1), d i) =
      fun d => ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ) := by
    ext d; simp
  rw [this]
  exact integrable_finsetSum _ fun i _ => coord_integrable P i

section general
variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

theorem eh_int (S : ℝ≥0) : Integrable (fun x : ℝ≥0 => max ((S : ℝ) - x) 0) μ := by
  refine Integrable.of_bound (by fun_prop) (S : ℝ) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [x.2]) S.2

theorem es_int (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (S : ℝ≥0) :
    Integrable (fun x : ℝ≥0 => max ((x : ℝ) - S) 0) μ := by
  refine hμ.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [S.2]) x.2

theorem eh_nonneg (S : ℝ≥0) : 0 ≤ expectedHolding μ S :=
  integral_nonneg fun _ => le_max_right _ _

theorem es_nonneg (S : ℝ≥0) : 0 ≤ expectedShortfall μ S :=
  integral_nonneg fun _ => le_max_right _ _

theorem eh_zero : expectedHolding μ 0 = 0 := by
  unfold expectedHolding
  have : (fun x : ℝ≥0 => max (((0 : ℝ≥0) : ℝ) - x) 0) = fun _ => 0 := by
    ext x; simp [x.2]
  rw [this, integral_zero]

theorem eh_ge (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (S : ℝ≥0) :
    (S : ℝ) - ∫ x : ℝ≥0, (x : ℝ) ∂μ ≤ expectedHolding μ S := by
  have h1 : ∫ x : ℝ≥0, ((S : ℝ) - x) ∂μ = (S : ℝ) - ∫ x : ℝ≥0, (x : ℝ) ∂μ := by
    rw [integral_sub (integrable_const _) hμ]; simp
  rw [← h1]
  exact integral_mono ((integrable_const _).sub hμ) (eh_int μ S) fun x => le_max_left _ _

theorem eh_mono {S S' : ℝ≥0} (h : S ≤ S') : expectedHolding μ S ≤ expectedHolding μ S' :=
  integral_mono (eh_int μ S) (eh_int μ S') fun x =>
    max_le_max (by have : (S : ℝ) ≤ S' := h; linarith) le_rfl

theorem eh_lip (S S' : ℝ≥0) :
    expectedHolding μ S' - expectedHolding μ S ≤ max ((S' : ℝ) - S) 0 := by
  unfold expectedHolding
  rw [← integral_sub (eh_int μ S') (eh_int μ S)]
  have : ∫ _x : ℝ≥0, max ((S' : ℝ) - S) 0 ∂μ = max ((S' : ℝ) - S) 0 := by simp
  rw [← this]
  refine integral_mono ((eh_int μ S').sub (eh_int μ S)) (integrable_const _) fun x => ?_
  simp only
  rcases le_total ((S' : ℝ) - x) 0 with h1 | h1 <;> rcases le_total ((S : ℝ) - x) 0 with h2 | h2 <;>
    simp only [max_eq_right h1, max_eq_left h1, max_eq_right h2, max_eq_left h2] <;>
    first
    | (rcases le_total ((S' : ℝ) - S) 0 with h3 | h3 <;>
        simp only [max_eq_right h3, max_eq_left h3] <;> linarith)

theorem es_lip (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (S S' : ℝ≥0) :
    expectedShortfall μ S' - expectedShortfall μ S ≤ max ((S : ℝ) - S') 0 := by
  unfold expectedShortfall
  rw [← integral_sub (es_int μ hμ S') (es_int μ hμ S)]
  have : ∫ _x : ℝ≥0, max ((S : ℝ) - S') 0 ∂μ = max ((S : ℝ) - S') 0 := by simp
  rw [← this]
  refine integral_mono ((es_int μ hμ S').sub (es_int μ hμ S)) (integrable_const _) fun x => ?_
  simp only
  rcases le_total ((x : ℝ) - S') 0 with h1 | h1 <;> rcases le_total ((x : ℝ) - S) 0 with h2 | h2 <;>
    simp only [max_eq_right h1, max_eq_left h1, max_eq_right h2, max_eq_left h2] <;>
    first
    | (rcases le_total ((S : ℝ) - S') 0 with h3 | h3 <;>
        simp only [max_eq_right h3, max_eq_left h3] <;> linarith)

end general

end PBS4H

namespace PBS4N
open PerishBaseStock.Outdating LostSalesOrderUpTo.Asymptotic PBS4H

theorem nv_lip (P : CappedBaseStock.DemandLaw) (c : Params) (S S' : ℝ≥0) :
    |nvCost P c S' - nvCost P c S| ≤ (c.h + c.p) * |(S' : ℝ) - S| := by
  have hh := c.h_pos.le
  have hp := c.p_pos.le
  have hi : Integrable (fun x : ℝ≥0 => (x : ℝ)) P.law := P.finiteMean
  have a1 := eh_lip P.law S S'
  have a2 := eh_lip P.law S' S
  have b1 := es_lip P.law hi S S'
  have b2 := es_lip P.law hi S' S
  have m1 : max ((S' : ℝ) - S) 0 ≤ |(S' : ℝ) - S| := max_le (le_abs_self _) (abs_nonneg _)
  have m2 : max ((S : ℝ) - S') 0 ≤ |(S' : ℝ) - S| :=
    max_le (by rw [abs_sub_comm]; exact le_abs_self _) (abs_nonneg _)
  have hA := abs_nonneg ((S' : ℝ) - S)
  unfold nvCost backorderCost
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (a2.trans m2) hh, mul_le_mul_of_nonneg_left (b2.trans m1) hp]
  · nlinarith [mul_le_mul_of_nonneg_left (a1.trans m1) hh, mul_le_mul_of_nonneg_left (b1.trans m2) hp]

theorem nv_continuous (P : CappedBaseStock.DemandLaw) (c : Params) : Continuous (nvCost P c) := by
  have hK : 0 ≤ c.h + c.p := by linarith [c.h_pos, c.p_pos]
  refine (LipschitzWith.of_dist_le_mul (K := ⟨c.h + c.p, hK⟩) fun S S' => ?_).continuous
  rw [Real.dist_eq, NNReal.dist_eq]
  have := nv_lip P c S' S
  exact this

end PBS4N

open PerishBaseStock.Outdating PBS4Z PBS4N in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) (St : ℝ≥0)
    (hSt : IsHeurMin P c θ St) :
    (∀ S : ℝ≥0, (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P → heurCost P c θ S = nvCost P c S) ∧
      (∃ S₀ : ℝ≥0, (S₀ : ℝ) ≤ (c.m : ℝ) * lowerSupport P ∧
        ∀ S : ℝ≥0, (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P → nvCost P c S₀ ≤ nvCost P c S) ∧
      (∀ S : ℝ≥0, (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P → heurCost P c θ St ≤ nvCost P c S) := by
  have h1 : ∀ S : ℝ≥0, (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P → heurCost P c θ S = nvCost P c S := by
    intro S hS
    unfold heurCost
    rw [excess_zero_of_le P c S hS, mul_zero, add_zero]
  refine ⟨h1, ?_, fun S hS => (hSt S).trans (h1 S hS).le⟩
  set K : Set ℝ≥0 := {S : ℝ≥0 | (S : ℝ) ≤ (c.m : ℝ) * lowerSupport P} with hK
  have hKeq : K = Set.Iic (Real.toNNReal ((c.m : ℝ) * lowerSupport P)) := by
    ext S
    simp only [hK, Set.mem_setOf_eq, Set.mem_Iic]
    rw [Real.le_toNNReal_iff_coe_le]
    exact (mul_nonneg (Nat.cast_nonneg _) (lowerSupport_nonneg P))
  have hKc : IsCompact K := by rw [hKeq, ← Set.Icc_bot]; exact isCompact_Icc
  have hKne : K.Nonempty := ⟨0, by
    simp only [hK, Set.mem_setOf_eq, NNReal.coe_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (lowerSupport_nonneg P)⟩
  obtain ⟨S₀, hS₀, hmin⟩ := hKc.exists_isMinOn hKne (nv_continuous P c).continuousOn
  exact ⟨S₀, hS₀, fun S hS => hmin hS⟩
