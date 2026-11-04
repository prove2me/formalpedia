-- Prove2me | solution 1 for PerishBaseStock.Outdating.eq_EC17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:54:29.096014+00:00
-- url     : https://prove2.me/submissions/af12599e-cd26-4b38-bcc0-c5fc8a1633ed

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

namespace PBS4M
open PerishBaseStock.Outdating LostSalesOrderUpTo.Asymptotic PBS4H PBS4Z PBS4N

theorem H_cont (P : CappedBaseStock.DemandLaw) (c : Params) :
    Continuous (excessOverLifetimeDemand P c) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun S S' => ?_).continuous
  rw [Real.dist_eq, NNReal.dist_eq]
  have a1 := eh_lip (leadTimeLaw P (c.m - 1)) S S'
  have a2 := eh_lip (leadTimeLaw P (c.m - 1)) S' S
  have m1 : max ((S' : ℝ) - S) 0 ≤ |(S : ℝ) - S'| :=
    max_le (by rw [abs_sub_comm]; exact le_abs_self _) (abs_nonneg _)
  have m2 : max ((S : ℝ) - S') 0 ≤ |(S : ℝ) - S'| := max_le (le_abs_self _) (abs_nonneg _)
  unfold excessOverLifetimeDemand
  rw [abs_le]; simp only [NNReal.coe_one, one_mul]
  constructor <;> linarith

theorem H_nonneg (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) :
    0 ≤ excessOverLifetimeDemand P c S := eh_nonneg _ S

theorem H_zero (P : CappedBaseStock.DemandLaw) (c : Params) :
    excessOverLifetimeDemand P c 0 = 0 := eh_zero _

theorem H_mono (P : CappedBaseStock.DemandLaw) (c : Params) {S S' : ℝ≥0} (h : S ≤ S') :
    excessOverLifetimeDemand P c S ≤ excessOverLifetimeDemand P c S' := eh_mono _ h

theorem nv_nonneg (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) : 0 ≤ nvCost P c S :=
  add_nonneg (mul_nonneg c.h_pos.le (eh_nonneg _ S)) (mul_nonneg c.p_pos.le (es_nonneg _ S))

theorem heur_cont (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) :
    Continuous (heurCost P c θ) :=
  (nv_continuous P c).add (continuous_const.mul (H_cont P c))

theorem heur_ge_nv (P : CappedBaseStock.DemandLaw) (c : Params) (θ S : ℝ≥0) :
    nvCost P c S ≤ heurCost P c θ S := by
  unfold heurCost
  have : 0 ≤ (θ : ℝ) / (c.m : ℝ) * excessOverLifetimeDemand P c S :=
    mul_nonneg (div_nonneg θ.2 (Nat.cast_nonneg _)) (H_nonneg P c S)
  linarith

theorem heur_zero (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) :
    heurCost P c θ 0 = nvCost P c 0 := by
  unfold heurCost; rw [H_zero, mul_zero, add_zero]

theorem minset_closed (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) :
    IsClosed {S : ℝ≥0 | IsHeurMin P c θ S} := by
  have : {S : ℝ≥0 | IsHeurMin P c θ S} = ⋂ S' : ℝ≥0, {S | heurCost P c θ S ≤ heurCost P c θ S'} := by
    ext S; simp [IsHeurMin]
  rw [this]
  exact isClosed_iInter fun S' => isClosed_le (heur_cont P c θ) continuous_const

theorem minset_nonempty (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) :
    {S : ℝ≥0 | IsHeurMin P c θ S}.Nonempty := by
  have hh := c.h_pos
  set μ : ℝ := ∫ x : ℝ≥0, (x : ℝ) ∂P.law
  set A := heurCost P c θ 0
  set R : ℝ≥0 := Real.toNNReal (μ + A / c.h + 1)
  have hKc : IsCompact (Set.Iic R) := by rw [← Set.Icc_bot]; exact isCompact_Icc
  obtain ⟨S₀, -, hmin⟩ := hKc.exists_isMinOn ⟨0, (zero_le : (0 : ℝ≥0) ≤ R)⟩ (heur_cont P c θ).continuousOn
  refine ⟨S₀, fun S' => ?_⟩
  by_cases hS' : S' ≤ R
  · exact hmin hS'
  · push_neg at hS'
    have h0 : heurCost P c θ S₀ ≤ A := hmin (show (0 : ℝ≥0) ∈ Set.Iic R from (zero_le : (0 : ℝ≥0) ≤ R))
    have hR : μ + A / c.h + 1 ≤ (S' : ℝ) := by
      have h2 : μ + A / c.h + 1 ≤ ((Real.toNNReal (μ + A / c.h + 1) : ℝ≥0) : ℝ) := Real.le_coe_toNNReal _
      have h3 : ((R : ℝ≥0) : ℝ) < S' := hS'
      linarith
    have hge := eh_ge P.law P.finiteMean S'
    have hnv : c.h * expectedHolding P.law S' ≤ nvCost P c S' := by
      unfold nvCost backorderCost
      have := mul_nonneg c.p_pos.le (es_nonneg P.law S')
      linarith
    have := heur_ge_nv P c θ S'
    have hA : A / c.h * c.h = A := div_mul_cancel₀ A hh.ne'
    have : c.h * ((S' : ℝ) - μ) ≥ c.h * (A / c.h + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hh.le
    nlinarith

theorem least_isMin (P : CappedBaseStock.DemandLaw) (c : Params) (θ : ℝ≥0) :
    IsHeurMin P c θ (leastHeurMin P c θ) :=
  (minset_closed P c θ).csInf_mem (minset_nonempty P c θ) (OrderBot.bddBelow _)

theorem least_le (P : CappedBaseStock.DemandLaw) (c : Params) (θ S : ℝ≥0) (h : IsHeurMin P c θ S) :
    leastHeurMin P c θ ≤ S :=
  csInf_le (OrderBot.bddBelow _) h

theorem least_anti (P : CappedBaseStock.DemandLaw) (c : Params) : Antitone (leastHeurMin P c) := by
  intro θ1 θ2 h12
  set S1 := leastHeurMin P c θ1
  set S2 := leastHeurMin P c θ2
  by_contra hcon
  push_neg at hcon
  have m1 := least_isMin P c θ1
  have m2 := least_isMin P c θ2
  have hH := H_mono P c hcon.le
  have hm : (0 : ℝ) < c.m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one c.one_le_m)
  have hd : 0 ≤ ((θ2 : ℝ) - θ1) / c.m := div_nonneg (by have : (θ1 : ℝ) ≤ θ2 := h12; linarith) hm.le
  have key : ∀ θ : ℝ≥0, ∀ S, heurCost P c θ S = nvCost P c S + (θ : ℝ) / c.m * excessOverLifetimeDemand P c S :=
    fun _ _ => rfl
  have hS1min : IsHeurMin P c θ2 S1 := by
    intro S'
    have a := m1 S2
    have b := m2 S'
    rw [key] at a b ⊢; rw [key] at a
    have e : (θ2 : ℝ) / c.m = (θ1 : ℝ) / c.m + ((θ2 : ℝ) - θ1) / c.m := by ring
    rw [e] at b ⊢
    nlinarith [mul_le_mul_of_nonneg_left hH hd]
  exact absurd (least_le P c θ2 S1 hS1min) (not_le.2 hcon)

end PBS4M

open PerishBaseStock.Outdating PBS4Z PBS4N PBS4M in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) :
    ∃ Sinf : ℝ≥0,
      Tendsto (fun θ : ℝ≥0 => leastHeurMin P c θ) atTop (𝓝 Sinf) ∧
      Tendsto (fun θ : ℝ≥0 => nvCost P c (leastHeurMin P c θ)) atTop (𝓝 (nvCost P c Sinf)) ∧
      nvMinBelow P c ≤ nvCost P c Sinf := by
  set Sinf := ⨅ θ : ℝ≥0, leastHeurMin P c θ
  have hT : Tendsto (fun θ : ℝ≥0 => leastHeurMin P c θ) atTop (𝓝 Sinf) :=
    tendsto_atTop_ciInf (least_anti P c) (OrderBot.bddBelow _)
  refine ⟨Sinf, hT, ((nv_continuous P c).tendsto Sinf).comp hT, ?_⟩
  have hle : ∀ θ, Sinf ≤ leastHeurMin P c θ := fun θ => ciInf_le (OrderBot.bddBelow _) θ
  have hm : (0 : ℝ) < c.m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one c.one_le_m)
  have hSm : (Sinf : ℝ) ≤ (c.m : ℝ) * lowerSupport P := by
    by_contra hcon
    push_neg at hcon
    have hpos := excess_pos_of_lt P c Sinf hcon
    set η := excessOverLifetimeDemand P c Sinf
    set N0 := nvCost P c 0
    have hN0 := nv_nonneg P c 0
    set θ : ℝ≥0 := Real.toNNReal (c.m * N0 / η + 1)
    have hθ : (c.m : ℝ) * N0 / η + 1 ≤ θ := Real.le_coe_toNNReal _
    have s1 := least_isMin P c θ 0
    rw [heur_zero] at s1
    have hnvS := nv_nonneg P c (leastHeurMin P c θ)
    have hHle := H_mono P c (hle θ)
    have e : heurCost P c θ (leastHeurMin P c θ) =
        nvCost P c (leastHeurMin P c θ) + (θ : ℝ) / c.m *
          excessOverLifetimeDemand P c (leastHeurMin P c θ) := rfl
    rw [e] at s1
    have hθpos : 0 < (θ : ℝ) := by
      have : 0 ≤ (c.m : ℝ) * N0 / η := by positivity
      linarith
    have h1 : (θ : ℝ) / c.m * η ≤ N0 := by
      have := mul_le_mul_of_nonneg_left hHle (div_nonneg hθpos.le hm.le)
      linarith
    have h2 : (c.m : ℝ) * N0 / η < θ := by linarith
    rw [div_lt_iff₀ hpos] at h2
    rw [div_mul_eq_mul_div, div_le_iff₀ hm] at h1
    nlinarith
  unfold nvMinBelow
  refine csInf_le ⟨0, ?_⟩ ⟨Sinf, hSm, rfl⟩
  rintro _ ⟨S, -, rfl⟩
  exact nv_nonneg P c S
