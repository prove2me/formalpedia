-- Prove2me | solution 1 for PerishBaseStock.Lifo.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:02:49.645648+00:00
-- url     : https://prove2.me/submissions/5c06f8d9-4fca-4bfd-b0e7-e58eafc7bfbc

import Definitions.Def_PerishBaseStock_Lifo_Heuristic
import Theorems.Thm_PerishBaseStock_Lifo_eq_27
import Theorems.Thm_PerishBaseStock_Lifo_ec_20
import Theorems.Thm_PerishBaseStock_Lifo_lemma_3
import Theorems.Thm_PerishBaseStock_Lifo_proposition_2
import Theorems.Thm_PerishBaseStock_Lifo_ec_21
import Theorems.Thm_PerishBaseStock_Lifo_ec_22

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5H

set_option linter.unusedSectionVars false

section general
variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

lemma int_hold (s : ℝ) : Integrable (fun x : ℝ≥0 => max (s - (x : ℝ)) 0) μ := by
  refine Integrable.mono' (integrable_const (|s|)) ?_ ?_
  · exact (Measurable.max (measurable_const.sub measurable_coe_nnreal_real)
      measurable_const).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self s, x.2]) (abs_nonneg s)

lemma EH_nonneg (S : ℝ≥0) : 0 ≤ expectedHolding μ S :=
  integral_nonneg fun _ => le_max_right _ _

lemma EH_mono {S S' : ℝ≥0} (h : S ≤ S') : expectedHolding μ S ≤ expectedHolding μ S' := by
  unfold expectedHolding
  refine integral_mono (int_hold μ S) (int_hold μ S') fun x => ?_
  have : (S : ℝ) ≤ S' := by exact_mod_cast h
  exact max_le_max (by linarith) le_rfl

lemma EH_zero : expectedHolding μ 0 = 0 := by
  unfold expectedHolding
  have : (fun x : ℝ≥0 => max (((0 : ℝ≥0) : ℝ) - (x : ℝ)) 0) = fun _ => 0 := by
    funext x; simp
  rw [this]; simp

/-- `|EH(S) - EH(S')| ≤ |S - S'|`. -/
lemma EH_lip (S S' : ℝ≥0) :
    |expectedHolding μ S - expectedHolding μ S'| ≤ |(S : ℝ) - S'| := by
  unfold expectedHolding
  rw [← integral_sub (int_hold μ S) (int_hold μ S')]
  calc |∫ x, (max ((S : ℝ) - x) 0 - max ((S' : ℝ) - x) 0) ∂μ|
      ≤ ∫ x, |max ((S : ℝ) - x) 0 - max ((S' : ℝ) - x) 0| ∂μ := by
        have := norm_integral_le_integral_norm
          (μ := μ) (fun x : ℝ≥0 => max ((S : ℝ) - x) 0 - max ((S' : ℝ) - x) 0)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∫ _x, |(S : ℝ) - S'| ∂μ := by
        refine integral_mono ((int_hold μ S).sub (int_hold μ S')).abs (integrable_const _)
          fun x => ?_
        exact abs_max_sub_max_le_max _ _ _ _ |>.trans (by
          simp only [sub_self, abs_zero]
          rw [max_eq_left (abs_nonneg _)]
          rw [show (S : ℝ) - x - (S' - x) = S - S' by ring])
    _ = |(S : ℝ) - S'| := by simp

lemma EH_cont : Continuous (fun S : ℝ≥0 => expectedHolding μ S) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun S S' => ?_)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, NNReal.dist_eq]
  exact EH_lip μ S S'

/-- Subgradient inequality for the holding term. -/
lemma EH_sub_ge {S0 S : ℝ≥0} (h : S0 ≤ S) :
    ((S : ℝ) - S0) * (μ (Set.Iic S0)).toReal ≤ expectedHolding μ S - expectedHolding μ S0 := by
  unfold expectedHolding
  rw [← integral_sub (int_hold μ S) (int_hold μ S0)]
  have hS : (S0 : ℝ) ≤ S := by exact_mod_cast h
  have hind : ∫ x, (Set.Iic S0).indicator (fun _ => ((S : ℝ) - S0)) x ∂μ
      = ((S : ℝ) - S0) * (μ (Set.Iic S0)).toReal := by
    rw [integral_indicator measurableSet_Iic, integral_const]
    simp [Measure.real, mul_comm]
  rw [← hind]
  refine integral_mono ((integrable_const _).indicator measurableSet_Iic)
    ((int_hold μ S).sub (int_hold μ S0)) fun x => ?_
  by_cases hx : x ≤ S0
  · rw [Set.indicator_of_mem (by exact hx)]
    have : (x : ℝ) ≤ S0 := by exact_mod_cast hx
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · rw [Set.indicator_of_notMem (by exact hx)]
    have : max ((S0 : ℝ) - x) 0 ≤ max ((S : ℝ) - x) 0 := max_le_max (by linarith) le_rfl
    linarith

end general

section demand
variable (P : CappedBaseStock.DemandLaw)

lemma int_short (s : ℝ) : Integrable (fun x : ℝ≥0 => max ((x : ℝ) - s) 0) P.law := by
  refine Integrable.mono' (P.finiteMean.add (integrable_const |s|)) ?_ ?_
  · exact (Measurable.max (measurable_coe_nnreal_real.sub measurable_const)
      measurable_const).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [neg_abs_le s]) (add_nonneg x.2 (abs_nonneg s))

lemma ES_nonneg (S : ℝ≥0) : 0 ≤ expectedShortfall P.law S :=
  integral_nonneg fun _ => le_max_right _ _

lemma ES_zero : expectedShortfall P.law 0 = CappedBaseStock.mean P := by
  unfold expectedShortfall CappedBaseStock.mean
  congr 1; funext x; simp

lemma ES_anti {S S' : ℝ≥0} (h : S ≤ S') :
    expectedShortfall P.law S' ≤ expectedShortfall P.law S := by
  unfold expectedShortfall
  refine integral_mono (int_short P S') (int_short P S) fun x => ?_
  have : (S : ℝ) ≤ S' := by exact_mod_cast h
  exact max_le_max (by linarith) le_rfl

lemma ES_lip (S S' : ℝ≥0) :
    |expectedShortfall P.law S - expectedShortfall P.law S'| ≤ |(S : ℝ) - S'| := by
  unfold expectedShortfall
  rw [← integral_sub (int_short P S) (int_short P S')]
  calc |∫ x, (max ((x : ℝ) - S) 0 - max ((x : ℝ) - S') 0) ∂P.law|
      ≤ ∫ x, |max ((x : ℝ) - S) 0 - max ((x : ℝ) - S') 0| ∂P.law := by
        have := norm_integral_le_integral_norm
          (μ := P.law) (fun x : ℝ≥0 => max ((x : ℝ) - S) 0 - max ((x : ℝ) - S') 0)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∫ _x, |(S : ℝ) - S'| ∂P.law := by
        refine integral_mono ((int_short P S).sub (int_short P S')).abs (integrable_const _)
          fun x => ?_
        refine abs_max_sub_max_le_max _ _ _ _ |>.trans ?_
        simp only [sub_self, abs_zero]
        rw [max_eq_left (abs_nonneg _)]
        rw [show (x : ℝ) - S - (x - S') = -(S - S') by ring, abs_neg]
    _ = |(S : ℝ) - S'| := by simp

lemma ES_cont : Continuous (fun S : ℝ≥0 => expectedShortfall P.law S) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun S S' => ?_)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, NNReal.dist_eq]
  exact ES_lip P S S'

/-- `E[(S-D)⁺] ≥ S - E[D]`. -/
lemma EH_ge_sub (S : ℝ≥0) : (S : ℝ) - CappedBaseStock.mean P ≤ expectedHolding P.law S := by
  unfold expectedHolding CappedBaseStock.mean
  have : (S : ℝ) - ∫ x : ℝ≥0, (x : ℝ) ∂P.law = ∫ x : ℝ≥0, ((S : ℝ) - x) ∂P.law := by
    rw [integral_sub (integrable_const _) P.finiteMean, integral_const]; simp
  rw [this]
  exact integral_mono ((integrable_const _).sub P.finiteMean) (int_hold P.law S)
    fun x => le_max_left _ _

/-- `E[(D-S)⁺] ≥ P(D > S + 1)`. -/
lemma ES_ge_tail (S : ℝ≥0) :
    (P.law (Set.Ioi (S + 1))).toReal ≤ expectedShortfall P.law S := by
  unfold expectedShortfall
  have hind : ∫ x, (Set.Ioi (S + 1)).indicator (fun _ => (1 : ℝ)) x ∂P.law
      = (P.law (Set.Ioi (S + 1))).toReal := by
    rw [integral_indicator measurableSet_Ioi, integral_const]
    simp [Measure.real]
  rw [← hind]
  refine integral_mono ((integrable_const _).indicator measurableSet_Ioi)
    (int_short P S) fun x => ?_
  by_cases hx : x ∈ Set.Ioi (S + 1)
  · rw [Set.indicator_of_mem hx]
    have : ((S : ℝ) + 1) < x := by exact_mod_cast hx
    exact le_max_of_le_left (by linarith)
  · rw [Set.indicator_of_notMem hx]; exact le_max_right _ _

/-- Subgradient inequality for the newsvendor cost. -/
lemma N_sub_ge (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) {S0 S : ℝ≥0} (hle : S0 ≤ S) :
    ((S : ℝ) - S0) * ((h + p) * (P.law (Set.Iic S0)).toReal - p) ≤
      backorderCost P.law h p S - backorderCost P.law h p S0 := by
  have h1 := EH_sub_ge P.law hle
  -- E[(D-S)⁺] - E[(D-S0)⁺] = (EH(S) - S + mean) - (EH(S0) - S0 + mean)
  have key : ∀ T : ℝ≥0, expectedShortfall P.law T = expectedHolding P.law T - T
      + CappedBaseStock.mean P := by
    intro T
    unfold expectedShortfall expectedHolding CappedBaseStock.mean
    suffices hs : ∫ x : ℝ≥0, max ((x : ℝ) - T) 0 ∂P.law - ∫ x : ℝ≥0, max ((T : ℝ) - x) 0 ∂P.law
        = ∫ x : ℝ≥0, (x : ℝ) ∂P.law - T by linarith
    rw [← integral_sub (int_short P T) (int_hold P.law T)]
    have : (fun x : ℝ≥0 => max ((x : ℝ) - T) 0 - max ((T : ℝ) - x) 0) =
        fun x : ℝ≥0 => (x : ℝ) - T := by
      funext x
      rcases le_total (x : ℝ) T with hx | hx
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    rw [this, integral_sub P.finiteMean (integrable_const _), integral_const]
    simp
  unfold backorderCost
  rw [key S, key S0]
  have hS : (S0 : ℝ) ≤ S := by exact_mod_cast hle
  nlinarith

/-- `F(S^NP) ≥ p/(p+h)`. -/
lemma cdf_snp_ge (h p : ℝ) (hh : 0 < h) (hp : 0 < p) :
    ENNReal.ofReal (p / (p + h)) ≤ P.law (Set.Iic (newsvendorLevel P.law h p)) := by
  set A := {S : ℝ≥0 | ENNReal.ofReal (p / (p + h)) ≤ distribution P.law S} with hA
  have hr1 : ENNReal.ofReal (p / (p + h)) < 1 := by
    rw [ENNReal.ofReal_lt_one]; rw [div_lt_one (by linarith)]; linarith
  -- A nonempty
  have hne : A.Nonempty := by
    have ht : Tendsto (fun n : ℕ => P.law (Set.Iic (n : ℝ≥0))) atTop (𝓝 (P.law (⋃ n : ℕ, Set.Iic (n : ℝ≥0)))) :=
      tendsto_measure_iUnion_atTop (fun a b hab => Set.Iic_subset_Iic.mpr (by exact_mod_cast hab))
    have hU : (⋃ n : ℕ, Set.Iic (n : ℝ≥0)) = Set.univ := by
      ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge x; exact ⟨n, hn⟩
    rw [hU, measure_univ] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hr1)).exists
    exact ⟨n, hn.le⟩
  have hup : ∀ a b : ℝ≥0, a ∈ A → a ≤ b → b ∈ A := fun a b ha hab =>
    le_trans ha (measure_mono (Set.Iic_subset_Iic.mpr hab))
  set s0 := sInf A
  have hmem : ∀ n : ℕ, s0 + 1 / ((n : ℝ≥0) + 1) ∈ A := by
    intro n
    have hpos : (0 : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) := by positivity
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right s0 hpos)
    exact hup a _ ha hlt.le
  have hI : Set.Iic s0 = ⋂ n : ℕ, Set.Iic (s0 + 1 / ((n : ℝ≥0) + 1)) := by
    ext x
    simp only [Set.mem_Iic, Set.mem_iInter]
    constructor
    · intro hx n; exact hx.trans (le_add_of_nonneg_right (by positivity))
    · intro hx
      by_contra hcon
      push Not at hcon
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (x : ℝ) - s0 by
        have : (s0 : ℝ) < x := by exact_mod_cast hcon
        linarith)
      have := hx n
      have : (x : ℝ) ≤ (s0 : ℝ) + 1 / ((n : ℝ) + 1) := by exact_mod_cast this
      linarith
  have ht : Tendsto (fun n : ℕ => P.law (Set.Iic (s0 + 1 / ((n : ℝ≥0) + 1)))) atTop
      (𝓝 (P.law (⋂ n : ℕ, Set.Iic (s0 + 1 / ((n : ℝ≥0) + 1))))) := by
    refine tendsto_measure_iInter_atTop (fun n => measurableSet_Iic.nullMeasurableSet)
      (fun a b hab => Set.Iic_subset_Iic.mpr ?_) ⟨0, measure_ne_top _ _⟩
    gcongr
  rw [← hI] at ht
  exact ge_of_tendsto' ht fun n => hmem n

end demand

end L5H


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5H
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

lemma meas_maxfun (k : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => (Finset.range (k + 1)).sup d) := by
  have h := Finset.measurable_range_sup'' (δ := CappedBaseStock.DemandPath) (α := ℝ≥0)
    (f := fun i (d : CappedBaseStock.DemandPath) => d i) (n := k)
    (fun i _ => measurable_pi_apply i)
  convert h using 1
  funext d
  rw [Finset.sup'_eq_sup]

lemma meas_sumfun (k : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => ∑ i ∈ Finset.range (k + 1), d i) :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

instance maxLaw_prob (P : CappedBaseStock.DemandLaw) (k : ℕ) :
    IsProbabilityMeasure (maxLaw P k) :=
  Measure.isProbabilityMeasure_map (meas_maxfun k).aemeasurable

instance leadTimeLaw_prob (P : CappedBaseStock.DemandLaw) (k : ℕ) :
    IsProbabilityMeasure (leadTimeLaw P k) :=
  Measure.isProbabilityMeasure_map (meas_sumfun k).aemeasurable

variable (P : CappedBaseStock.DemandLaw)

lemma law_eq_map0 : P.law = (CappedBaseStock.demandPathLaw P).map (fun d => d 0) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) 0).map_eq.symm

/-- `E[(S - g)⁺] ≤ E[(S - D_1)⁺]` when `g ≥ D_1` pathwise. -/
lemma EH_map_le (g : CappedBaseStock.DemandPath → ℝ≥0) (hg : Measurable g)
    (hge : ∀ d, d 0 ≤ g d) (S : ℝ≥0) :
    expectedHolding ((CappedBaseStock.demandPathLaw P).map g) S ≤ expectedHolding P.law S := by
  have : IsProbabilityMeasure ((CappedBaseStock.demandPathLaw P).map g) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  have hf : Measurable (fun x : ℝ≥0 => max ((S : ℝ) - x) 0) := by fun_prop
  unfold expectedHolding
  rw [integral_map hg.aemeasurable hf.aestronglyMeasurable]
  conv_rhs => rw [law_eq_map0 P]
  have h0 : Measurable (fun d : CappedBaseStock.DemandPath => d 0) := measurable_pi_apply 0
  rw [integral_map h0.aemeasurable hf.aestronglyMeasurable]
  have i1 : Integrable (fun d : CappedBaseStock.DemandPath => max ((S : ℝ) - g d) 0)
      (CappedBaseStock.demandPathLaw P) :=
    (int_hold ((CappedBaseStock.demandPathLaw P).map g) S).comp_measurable hg
  have i2 : Integrable (fun d : CappedBaseStock.DemandPath => max ((S : ℝ) - d 0) 0)
      (CappedBaseStock.demandPathLaw P) := by
    have := (int_hold P.law S)
    rw [law_eq_map0 P] at this
    exact this.comp_measurable h0
  refine integral_mono i1 i2 fun d => ?_
  have : ((d 0 : ℝ≥0) : ℝ) ≤ g d := by exact_mod_cast hge d
  exact max_le_max (by linarith) le_rfl

lemma EH_max_le (k : ℕ) (S : ℝ≥0) :
    expectedHolding (maxLaw P k) S ≤ expectedHolding P.law S :=
  EH_map_le P _ (meas_maxfun k)
    (fun d => Finset.le_sup (f := d) (Finset.mem_range.mpr (Nat.succ_pos k))) S

lemma N_ge_snp (c : Params) (hc : c.Standing) {S : ℝ≥0} (hS : snp P c ≤ S) :
    backorderCost P.law c.h c.p (snp P c) ≤ backorderCost P.law c.h c.p S := by
  have h1 := N_sub_ge P c.h c.p hc.h_pos.le hc.p_pos.le hS
  have hF := cdf_snp_ge P c.h c.p hc.h_pos hc.p_pos
  have hF' : c.p / (c.p + c.h) ≤ (P.law (Set.Iic (snp P c))).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hF
  have hph : 0 < c.p + c.h := by linarith [hc.h_pos, hc.p_pos]
  have : 0 ≤ (c.h + c.p) * (P.law (Set.Iic (snp P c))).toReal - c.p := by
    rw [div_le_iff₀ hph] at hF'
    nlinarith
  have hS' : ((snp P c : ℝ≥0) : ℝ) ≤ S := by exact_mod_cast hS
  nlinarith [mul_nonneg (sub_nonneg.2 hS') this]

lemma F_snp_pos (c : Params) (hc : c.Standing) : 0 < (P.law (Set.Iic (snp P c))).toReal := by
  have hF := cdf_snp_ge P c.h c.p hc.h_pos hc.p_pos
  have hF' : c.p / (c.p + c.h) ≤ (P.law (Set.Iic (snp P c))).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hF
  have : 0 < c.p / (c.p + c.h) := div_pos hc.p_pos (by linarith [hc.h_pos, hc.p_pos])
  linarith

lemma tildeC_cont (c : Params) : Continuous (fun S : ℝ≥0 => tildeC P c S) := by
  unfold tildeC backorderCost
  exact ((continuous_const.mul (EH_cont P.law)).add (continuous_const.mul (ES_cont P))).add
    (continuous_const.mul (EH_cont _))

lemma tilde_exists (c : Params) (hc : c.Standing) :
    ∃ St : ℝ≥0, St ≤ snp P c ∧ IsTildeMinimizer P c St := by
  obtain ⟨St, hmem, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := snp P c)).exists_isMinOn
    (Set.nonempty_Icc.2 (by positivity)) (tildeC_cont P c).continuousOn
  refine ⟨St, hmem.2, fun S => ?_⟩
  rcases le_total S (snp P c) with hS | hS
  · exact hmin ⟨by positivity, hS⟩
  · refine (hmin ⟨by positivity, le_rfl⟩).trans ?_
    unfold tildeC
    have h1 := N_ge_snp P c hc hS
    have h2 := EH_mono (leadTimeLaw P (c.m - 1)) hS
    have hθm : 0 ≤ c.θ / c.m := div_nonneg hc.θ_nonneg (Nat.cast_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left h2 hθm]

lemma hatObjective_eq (c : Params) (S : ℝ≥0) :
    hatObjective P c S = backorderCost P.law c.h c.p S +
      c.θ / c.m * (expectedHolding P.law S + expectedHolding (maxLaw P (c.m - 1)) S) / 2 := by
  unfold hatObjective hatCL hatCU backorderCost
  ring

lemma hat_le_snp (c : Params) (hc : c.Standing) (hθ : 0 < c.θ) (Sh : ℝ≥0)
    (hSh : IsHatMinimizer P c Sh) : Sh ≤ snp P c := by
  by_contra hcon
  push Not at hcon
  have hmin := hSh (snp P c)
  rw [hatObjective_eq, hatObjective_eq] at hmin
  have h1 := N_ge_snp P c hc hcon.le
  have h2 := EH_mono (maxLaw P (c.m - 1)) hcon.le
  have h3 := EH_sub_ge P.law hcon.le
  have hF := F_snp_pos P c hc
  have hd : (0 : ℝ) < (Sh : ℝ) - snp P c := by
    have : ((snp P c : ℝ≥0) : ℝ) < Sh := by exact_mod_cast hcon
    linarith
  have hm : (0 : ℝ) < c.m := by exact_mod_cast hc.one_le_m
  have hθm : 0 < c.θ / c.m := div_pos hθ hm
  have h4 : 0 < expectedHolding P.law Sh - expectedHolding P.law (snp P c) :=
    lt_of_lt_of_le (mul_pos hd hF) h3
  nlinarith [mul_lt_mul_of_pos_left h4 hθm, mul_le_mul_of_nonneg_left h2 hθm.le]

end L5H


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5H
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw)

lemma OPT_le_bs (c : Params) (S : ℝ≥0) : OPT P c ≤ baseStockCost P c S :=
  iInf_le (fun π => policyCost P c π) (baseStock c.m S)

lemma bs_lt_top (c : Params) (hc : c.Standing) (S : ℝ≥0) : baseStockCost P c S < ⊤ :=
  ((lemma_3 P c hc S).2).trans_lt ENNReal.ofReal_lt_top

theorem part_a (c : Params) (hc : c.Standing) (Sh : ℝ≥0) (hSh : IsHatMinimizer P c Sh) :
    baseStockCost P c Sh ≤
      OPT P c + ENNReal.ofReal (3 * c.θ * expectedHolding P.law (snp P c) / (2 * c.m)) := by
  obtain ⟨St, hStle, hSt⟩ := tilde_exists P c hc
  refine (eq_27 P c hc Sh St hSh hSt).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hm : (0 : ℝ) < c.m := by exact_mod_cast hc.one_le_m
  rcases hc.θ_nonneg.eq_or_lt with h0 | hθ
  · rw [← h0]; simp
  · have hSh' := hat_le_snp P c hc hθ Sh hSh
    have e1 := EH_mono P.law hSh'
    have e2 := EH_mono P.law hStle
    have e3 := EH_nonneg (maxLaw P (c.m - 1)) Sh
    have e4 := EH_max_le P (c.m - 1) St
    have e5 := EH_nonneg (leadTimeLaw P (c.m - 1)) St
    rw [show 3 * c.θ * expectedHolding P.law (snp P c) / (2 * c.m) =
      c.θ / (2 * c.m) * (3 * expectedHolding P.law (snp P c)) by field_simp]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith

/-- For unbounded demand, the newsvendor cost grows uniformly with `p`. -/
lemma N_grows (hU : DemandUnbounded P) (h : ℝ) (hh : 0 < h) (M : ℝ) :
    ∃ p0 : ℝ, 0 < p0 ∧ ∀ p : ℝ, p0 ≤ p → ∀ S : ℝ≥0, M ≤ backorderCost P.law h p S := by
  set K : ℝ≥0 := Real.toNNReal (M / h + CappedBaseStock.mean P)
  set τ := (P.law (Set.Ioi (K + 1))).toReal
  have hτ : 0 < τ := by
    have h1 := hU (K + 1)
    have h2 : P.law (Set.Ioi (K + 1)) = 1 - P.law (Set.Iic (K + 1)) := by
      rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
    have h3 : 0 < P.law (Set.Ioi (K + 1)) := by
      rw [h2]; exact tsub_pos_of_lt h1
    exact ENNReal.toReal_pos h3.ne' (measure_ne_top _ _)
  refine ⟨max 1 (M / τ), lt_max_of_lt_left one_pos, fun p hp S => ?_⟩
  have hp0 : 0 < p := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hp)
  unfold backorderCost
  have eh := EH_nonneg P.law S
  have es := ES_nonneg P S
  rcases le_total K S with hKS | hSK
  · have h1 := EH_ge_sub P S
    have hK : M / h + CappedBaseStock.mean P ≤ (K : ℝ) := Real.le_coe_toNNReal _
    have hK' : (K : ℝ) ≤ S := by exact_mod_cast hKS
    have : M ≤ h * expectedHolding P.law S := by
      have : M / h ≤ expectedHolding P.law S := by linarith
      rwa [div_le_iff₀ hh, mul_comm] at this
    nlinarith [mul_nonneg hp0.le es]
  · have h1 := ES_anti P hSK
    have h2 := ES_ge_tail P K
    have h3 : M / τ ≤ p := (le_max_right _ _).trans hp
    have : M ≤ p * τ := by rwa [div_le_iff₀ hτ] at h3
    nlinarith [mul_nonneg hh.le eh, mul_le_mul_of_nonneg_left (h2.trans h1) hp0.le]

theorem part_b (hU : DemandUnbounded P) (c : Params) (hc : c.Standing) (Sh : ℝ → ℝ≥0)
    (hSh : ∀ p : ℝ, 0 < p → IsHatMinimizer P { c with p := p } (Sh p)) :
    (∀ᶠ p in atTop, baseStockCost P { c with p := p } (Sh p) < ⊤ ∧
        0 < OPT P { c with p := p } ∧ OPT P { c with p := p } < ⊤) ∧
      Tendsto (fun p : ℝ => ((baseStockCost P { c with p := p } (Sh p)).toReal
          - (OPT P { c with p := p }).toReal) / (OPT P { c with p := p }).toReal)
        atTop (𝓝 0) := by
  have hcp : ∀ p : ℝ, 0 < p → ({ c with p := p } : Params).Standing := fun p hp =>
    ⟨hc.one_le_m, hc.h_pos, hp, hc.θ_nonneg⟩
  -- lower bound on OPT via Proposition 2
  have hlow : ∀ p : ℝ, 0 < p → ∀ M : ℝ, (∀ S : ℝ≥0, M ≤ backorderCost P.law c.h p S) →
      ENNReal.ofReal M ≤ OPT P { c with p := p } := by
    intro p hp M hM
    obtain ⟨St, -, hSt⟩ := tilde_exists P _ (hcp p hp)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (proposition_2 P _ (hcp p hp) St hSt)
    unfold tildeC
    have := EH_nonneg (leadTimeLaw P (c.m - 1)) St
    have hθm : 0 ≤ c.θ / c.m := div_nonneg hc.θ_nonneg (Nat.cast_nonneg _)
    have := hM St
    simp only at this ⊢
    nlinarith [mul_nonneg hθm (EH_nonneg (leadTimeLaw P (c.m - 1)) St)]
  set G : ℝ := ((c.m : ℝ) - 1) * c.θ / c.m * CappedBaseStock.mean P
  have hgap : ∀ p : ℝ, 0 < p → baseStockCost P { c with p := p } (Sh p) ≤
      OPT P { c with p := p } + ENNReal.ofReal G := by
    intro p hp
    obtain ⟨St, -, hSt⟩ := tilde_exists P _ (hcp p hp)
    have h := ec_20 P _ (hcp p hp) (Sh p) St (hSh p hp) hSt
    exact h.1.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal h.2))
  obtain ⟨p1, hp1, hN1⟩ := N_grows P hU c.h hc.h_pos 1
  have hev : ∀ᶠ p in atTop, baseStockCost P { c with p := p } (Sh p) < ⊤ ∧
      0 < OPT P { c with p := p } ∧ OPT P { c with p := p } < ⊤ := by
    filter_upwards [eventually_ge_atTop p1] with p hp
    have hp0 : 0 < p := lt_of_lt_of_le hp1 hp
    have hC := bs_lt_top P _ (hcp p hp0) (Sh p)
    refine ⟨hC, ?_, (OPT_le_bs P _ (Sh p)).trans_lt hC⟩
    exact lt_of_lt_of_le (by simp) (hlow p hp0 1 (hN1 p hp))
  refine ⟨hev, ?_⟩
  -- OPT.toReal → ∞
  have hOinf : Tendsto (fun p : ℝ => (OPT P { c with p := p }).toReal) atTop atTop := by
    refine tendsto_atTop.2 fun M => ?_
    obtain ⟨p2, hp2, hN2⟩ := N_grows P hU c.h hc.h_pos M
    filter_upwards [eventually_ge_atTop p2, hev] with p hp hpev
    have hp0 : 0 < p := lt_of_lt_of_le hp2 hp
    have h := hlow p hp0 M (hN2 p hp)
    rcases le_total M 0 with hM | hM
    · exact hM.trans ENNReal.toReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal hpev.2.2.ne).1 h
  have hup : Tendsto (fun p : ℝ => G / (OPT P { c with p := p }).toReal) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hOinf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0, hev] with p hp hpev
    refine div_nonneg (sub_nonneg.2 ?_) ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono hpev.1.ne (OPT_le_bs P _ (Sh p))
  · filter_upwards [eventually_gt_atTop 0, hev] with p hp hpev
    have hpos : 0 < (OPT P { c with p := p }).toReal :=
      ENNReal.toReal_pos hpev.2.1.ne' hpev.2.2.ne
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have h := hgap p hp
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hpev.2.2.ne, ENNReal.ofReal_ne_top⟩) h
    have hG : 0 ≤ G := by
      have hm1 : (1 : ℝ) ≤ c.m := by exact_mod_cast hc.one_le_m
      have := CappedBaseStock.DemandLaw.positiveMean P
      have hmean : 0 ≤ CappedBaseStock.mean P := this.le
      have : 0 ≤ ((c.m : ℝ) - 1) * c.θ / c.m := by
        apply div_nonneg (mul_nonneg (by linarith) hc.θ_nonneg) (by linarith)
      exact mul_nonneg this hmean
    rw [ENNReal.toReal_add hpev.2.2.ne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hG] at h2
    linarith

theorem part_c (h0 : lowerSupport P = 0) (c : Params) (hc : c.Standing) (Sh : ℝ → ℝ≥0)
    (hSh : ∀ θ : ℝ, 0 ≤ θ → IsHatMinimizer P { c with θ := θ } (Sh θ)) :
    (∀ θ : ℝ, 0 ≤ θ → baseStockCost P { c with θ := θ } (Sh θ) < ⊤ ∧
        OPT P { c with θ := θ } < ⊤) ∧
      Tendsto (fun θ : ℝ => (baseStockCost P { c with θ := θ } (Sh θ)).toReal
          - (OPT P { c with θ := θ }).toReal) atTop (𝓝 0) := by
  have hcθ : ∀ θ : ℝ, 0 ≤ θ → ({ c with θ := θ } : Params).Standing := fun θ hθ =>
    ⟨hc.one_le_m, hc.h_pos, hc.p_pos, hθ⟩
  have hfin : ∀ θ : ℝ, 0 ≤ θ → baseStockCost P { c with θ := θ } (Sh θ) < ⊤ ∧
      OPT P { c with θ := θ } < ⊤ := fun θ hθ =>
    ⟨bs_lt_top P _ (hcθ θ hθ) (Sh θ),
      (OPT_le_bs P _ (Sh θ)).trans_lt (bs_lt_top P _ (hcθ θ hθ) (Sh θ))⟩
  refine ⟨hfin, ?_⟩
  set St : ℝ → ℝ≥0 := fun θ => Classical.epsilon (fun S => IsTildeMinimizer P { c with θ := θ } S)
  have hSt : ∀ θ : ℝ, 0 ≤ θ → IsTildeMinimizer P { c with θ := θ } (St θ) := by
    intro θ hθ
    obtain ⟨S, -, hS⟩ := tilde_exists P _ (hcθ θ hθ)
    exact Classical.epsilon_spec (p := fun S => IsTildeMinimizer P { c with θ := θ } S) ⟨S, hS⟩
  obtain ⟨-, L, hL, hLge⟩ := ec_21 P c hc St hSt
  have h22 := ec_22 P c hc Sh hSh
  -- the infimum is `N(0) = p E[D]`
  have hinf : (⨅ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
      backorderCost P.law c.h c.p S.val) = c.p * CappedBaseStock.mean P := by
    have : Nonempty {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)} :=
      ⟨⟨0, by rw [h0]; simp⟩⟩
    have : (fun S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)} =>
        backorderCost P.law c.h c.p S.val) = fun _ => backorderCost P.law c.h c.p 0 := by
      funext S
      have : (S.val : ℝ) ≤ 0 := by
        calc (S.val : ℝ) ≤ c.m * (lowerSupport P : ℝ) := S.2
          _ = 0 := by rw [h0]; simp
      have : S.val = 0 := by
        exact_mod_cast le_antisymm this (by positivity)
      rw [this]
    rw [this, ciInf_const]
    unfold backorderCost
    rw [EH_zero, ES_zero]; ring
  rw [hinf] at hLge
  rw [h0] at h22
  simp only [NNReal.coe_zero, sub_zero] at h22
  -- convergence of the base-stock cost to `L`
  have hle : ∀ᶠ θ in atTop, OPT P { c with θ := θ } ≤ baseStockCost P { c with θ := θ } (Sh θ) :=
    Eventually.of_forall fun θ => OPT_le_bs P _ (Sh θ)
  have hlim : L ≤ liminf (fun θ : ℝ => baseStockCost P { c with θ := θ } (Sh θ)) atTop := by
    rw [← hL.liminf_eq]
    exact liminf_le_liminf hle
  have hlsup : limsup (fun θ : ℝ => baseStockCost P { c with θ := θ } (Sh θ)) atTop ≤ L :=
    h22.trans hLge
  have hC : Tendsto (fun θ : ℝ => baseStockCost P { c with θ := θ } (Sh θ)) atTop (𝓝 L) :=
    tendsto_of_le_liminf_of_limsup_le hlim hlsup
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hlim.trans liminf_le_limsup).trans h22)
  have h1 := (ENNReal.tendsto_toReal hLtop).comp hC
  have h2 := (ENNReal.tendsto_toReal hLtop).comp hL
  have := h1.sub h2
  simpa using this

end L5H


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic
open PerishBaseStock.Lifo

theorem solution (P : CappedBaseStock.DemandLaw) :
    (∀ (c : Params), c.Standing → ∀ Sh : ℝ≥0, IsHatMinimizer P c Sh →
      baseStockCost P c Sh ≤
        OPT P c + ENNReal.ofReal (3 * c.θ * expectedHolding P.law (snp P c) / (2 * c.m))) ∧
    (DemandUnbounded P → ∀ (c : Params), c.Standing → ∀ Sh : ℝ → ℝ≥0,
      (∀ p : ℝ, 0 < p → IsHatMinimizer P { c with p := p } (Sh p)) →
        (∀ᶠ p in atTop, baseStockCost P { c with p := p } (Sh p) < ⊤ ∧
            0 < OPT P { c with p := p } ∧ OPT P { c with p := p } < ⊤) ∧
          Tendsto (fun p : ℝ => ((baseStockCost P { c with p := p } (Sh p)).toReal
              - (OPT P { c with p := p }).toReal) / (OPT P { c with p := p }).toReal)
            atTop (𝓝 0)) ∧
    (lowerSupport P = 0 → ∀ (c : Params), c.Standing → ∀ Sh : ℝ → ℝ≥0,
      (∀ θ : ℝ, 0 ≤ θ → IsHatMinimizer P { c with θ := θ } (Sh θ)) →
        (∀ θ : ℝ, 0 ≤ θ → baseStockCost P { c with θ := θ } (Sh θ) < ⊤ ∧
            OPT P { c with θ := θ } < ⊤) ∧
          Tendsto (fun θ : ℝ => (baseStockCost P { c with θ := θ } (Sh θ)).toReal
              - (OPT P { c with θ := θ }).toReal) atTop (𝓝 0)) :=
  ⟨fun c hc Sh hSh => L5H.part_a P c hc Sh hSh,
    fun hU c hc Sh hSh => L5H.part_b P hU c hc Sh hSh,
    fun h0 c hc Sh hSh => L5H.part_c P h0 c hc Sh hSh⟩
