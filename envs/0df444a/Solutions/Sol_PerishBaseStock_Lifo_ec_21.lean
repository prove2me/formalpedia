-- Prove2me | solution 1 for PerishBaseStock.Lifo.ec_21
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:35:35.845415+00:00
-- url     : https://prove2.me/submissions/dc8225f7-fcd3-4c80-bec9-d1fb432cbb8b

import Definitions.Def_PerishBaseStock_Lifo_Heuristic
import Theorems.Thm_PerishBaseStock_Outdating_eq_EC16
import Theorems.Thm_PerishBaseStock_Outdating_eq_EC17
import Theorems.Thm_PerishBaseStock_Outdating_eq_24

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

lemma law_eq_map (i : ℕ) : P.law = (CappedBaseStock.demandPathLaw P).map (fun d => d i) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i).map_eq.symm

lemma int_coord (i : ℕ) : Integrable (fun d : CappedBaseStock.DemandPath => ((d i : ℝ≥0) : ℝ))
    (CappedBaseStock.demandPathLaw P) := by
  have := P.finiteMean
  rw [law_eq_map P i] at this
  exact this.comp_measurable (measurable_pi_apply i)

lemma integral_coord (i : ℕ) : ∫ d, ((d i : ℝ≥0) : ℝ) ∂(CappedBaseStock.demandPathLaw P)
    = CappedBaseStock.mean P := by
  unfold CappedBaseStock.mean
  conv_rhs => rw [law_eq_map P i]
  rw [integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]

/-- Integrability of `x` under the law of `g` when `g ≤ Σ_{i ≤ k} D_i`. -/
lemma int_id_map (g : CappedBaseStock.DemandPath → ℝ≥0) (hg : Measurable g) (k : ℕ)
    (hle : ∀ d, g d ≤ ∑ i ∈ Finset.range (k + 1), d i) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) ((CappedBaseStock.demandPathLaw P).map g) := by
  rw [integrable_map_measure (by fun_prop) hg.aemeasurable]
  refine Integrable.mono' (integrable_finsetSum (Finset.range (k + 1)) fun i _ => int_coord P i)
    (by fun_prop) (Eventually.of_forall fun d => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs, NNReal.abs_eq]
  have := hle d
  have : ((g d : ℝ≥0) : ℝ) ≤ ((∑ i ∈ Finset.range (k + 1), d i : ℝ≥0) : ℝ) := by exact_mod_cast this
  simpa [NNReal.coe_sum] using this

lemma int_short_gen (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (s : ℝ) :
    Integrable (fun x : ℝ≥0 => max ((x : ℝ) - s) 0) μ := by
  refine Integrable.mono' (hμ.add (integrable_const |s|)) ?_ ?_
  · exact (Measurable.max (measurable_coe_nnreal_real.sub measurable_const)
      measurable_const).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [neg_abs_le s]) (add_nonneg x.2 (abs_nonneg s))

/-- `x⁺ = x + (-x)⁺` in expectation: `E[(X-S)⁺] = E[(S-X)⁺] - S + E[X]`. -/
lemma ES_eq_gen (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (T : ℝ≥0) :
    expectedShortfall μ T = expectedHolding μ T - T + ∫ x : ℝ≥0, (x : ℝ) ∂μ := by
  unfold expectedShortfall expectedHolding
  suffices hs : ∫ x : ℝ≥0, max ((x : ℝ) - T) 0 ∂μ - ∫ x : ℝ≥0, max ((T : ℝ) - x) 0 ∂μ
      = ∫ x : ℝ≥0, (x : ℝ) ∂μ - T by linarith
  rw [← integral_sub (int_short_gen μ hμ T) (int_hold μ T)]
  have : (fun x : ℝ≥0 => max ((x : ℝ) - T) 0 - max ((T : ℝ) - x) 0) =
      fun x : ℝ≥0 => (x : ℝ) - T := by
    funext x
    rcases le_total (x : ℝ) T with hx | hx
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [this, integral_sub hμ (integrable_const _), integral_const]
  simp

lemma max_le_sum (k : ℕ) (d : CappedBaseStock.DemandPath) :
    (Finset.range (k + 1)).sup d ≤ ∑ i ∈ Finset.range (k + 1), d i :=
  Finset.sup_le fun i hi => Finset.single_le_sum (f := d) (fun _ _ => zero_le) hi

lemma int_maxLaw (k : ℕ) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (maxLaw P k) :=
  int_id_map P _ (meas_maxfun k) k (max_le_sum k)

lemma int_leadLaw (k : ℕ) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (leadTimeLaw P k) :=
  int_id_map P _ (meas_sumfun k) k (fun _ => le_rfl)

lemma mean_leadLaw (k : ℕ) :
    ∫ x : ℝ≥0, (x : ℝ) ∂(leadTimeLaw P k) = (k + 1) * CappedBaseStock.mean P := by
  unfold leadTimeLaw
  rw [integral_map (meas_sumfun k).aemeasurable (by fun_prop)]
  simp only [NNReal.coe_sum]
  rw [integral_finsetSum _ fun i _ => int_coord P i]
  simp [integral_coord P]

/-- `E[(g₁ - S)⁺] ≤ E[(g₂ - S)⁺]` when `g₁ ≤ g₂ ≤ Σ_{i≤k} D_i`. -/
lemma ES_map_mono (g₁ g₂ : CappedBaseStock.DemandPath → ℝ≥0) (h1 : Measurable g₁)
    (h2 : Measurable g₂) (k : ℕ) (hle : ∀ d, g₁ d ≤ g₂ d)
    (hle2 : ∀ d, g₂ d ≤ ∑ i ∈ Finset.range (k + 1), d i) (S : ℝ≥0) :
    expectedShortfall ((CappedBaseStock.demandPathLaw P).map g₁) S ≤
      expectedShortfall ((CappedBaseStock.demandPathLaw P).map g₂) S := by
  have : IsProbabilityMeasure ((CappedBaseStock.demandPathLaw P).map g₁) :=
    Measure.isProbabilityMeasure_map h1.aemeasurable
  have : IsProbabilityMeasure ((CappedBaseStock.demandPathLaw P).map g₂) :=
    Measure.isProbabilityMeasure_map h2.aemeasurable
  have hf : Measurable (fun x : ℝ≥0 => max ((x : ℝ) - S) 0) := by fun_prop
  have i1 := (int_short_gen _ (int_id_map P g₁ h1 k (fun d => (hle d).trans (hle2 d))) S)
  have i2 := (int_short_gen _ (int_id_map P g₂ h2 k hle2) S)
  unfold expectedShortfall
  rw [integral_map h1.aemeasurable hf.aestronglyMeasurable,
    integral_map h2.aemeasurable hf.aestronglyMeasurable]
  refine integral_mono (i1.comp_measurable h1) (i2.comp_measurable h2) fun d => ?_
  have : ((g₁ d : ℝ≥0) : ℝ) ≤ g₂ d := by exact_mod_cast hle d
  exact max_le_max (by linarith) le_rfl

lemma ES_P_le_max (k : ℕ) (S : ℝ≥0) :
    expectedShortfall P.law S ≤ expectedShortfall (maxLaw P k) S := by
  rw [law_eq_map P 0]
  exact ES_map_mono P _ _ (measurable_pi_apply 0) (meas_maxfun k) k
    (fun d => Finset.le_sup (f := d) (Finset.mem_range.mpr (Nat.succ_pos k)))
    (max_le_sum k) S

lemma ES_max_le_sum (k : ℕ) (S : ℝ≥0) :
    expectedShortfall (maxLaw P k) S ≤ expectedShortfall (leadTimeLaw P k) S :=
  ES_map_mono P _ _ (meas_maxfun k) (meas_sumfun k) k (max_le_sum k) (fun _ => le_rfl) S

end L5H


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable {m : ℕ}

lemma cum_zero (x : PerishBaseStock.Lifetime.State m) : cum x 0 = 0 := by simp [cum]

lemma cum_of_ge (x : PerishBaseStock.Lifetime.State m) (i : ℕ) (hi : m ≤ i) : cum x i = 0 := by
  unfold cum; rw [dif_neg]; omega

lemma level_of_lt (x : PerishBaseStock.Lifetime.State m) (q : ℝ) (i : ℕ) (hi : i < m) :
    level x q i = cum x i := by simp [level, hi]

lemma level_m (x : PerishBaseStock.Lifetime.State m) (q : ℝ) :
    level x q m = cum x (m - 1) + q := by simp [level]

lemma cum_lifoStep (x : PerishBaseStock.Lifetime.State m) (q d : ℝ) (i : ℕ)
    (h0 : 0 < i) (hi : i < m) :
    cum (lifoStep x q d) i = min (leftover x q d) (level x q (i + 1)) - outdate x q d := by
  unfold cum
  rw [dif_pos ⟨h0, hi⟩]
  simp only [lifoStep]
  congr 3
  omega

/-- `x_{t+1,j-1} + o_t = min{(x_{t,m}-D)⁺, x_{t,j}}` for `1 ≤ j ≤ m`. -/
lemma key (x : PerishBaseStock.Lifetime.State m) (q d q' : ℝ) (j : ℕ) (h1 : 1 ≤ j)
    (hj : j ≤ m) :
    level (lifoStep x q d) q' (j - 1) + outdate x q d = min (leftover x q d) (level x q j) := by
  rw [level_of_lt _ _ _ (by omega)]
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · subst h; simp [cum_zero, outdate]
  · rw [cum_lifoStep _ _ _ _ (by omega) (by omega)]
    have : j - 1 + 1 = j := by omega
    rw [this]; ring

lemma cum_empty (i : ℕ) : cum (PerishBaseStock.Lifetime.emptyState m) i = 0 := by
  unfold cum; split_ifs <;> rfl

/-- Monotone nonnegative cumulative levels. -/
def Inv (x : PerishBaseStock.Lifetime.State m) : Prop :=
  ∀ i j, i ≤ j → j < m → cum x i ≤ cum x j

lemma Inv.nonneg {x : PerishBaseStock.Lifetime.State m} (h : Inv x) (i : ℕ) : 0 ≤ cum x i := by
  by_cases hi : i < m
  · have := h 0 i (Nat.zero_le _) hi; rwa [cum_zero] at this
  · rw [cum_of_ge _ _ (by omega)]

lemma Inv.level_mono {x : PerishBaseStock.Lifetime.State m} (h : Inv x) {q : ℝ} (hq : 0 ≤ q)
    (hm : 1 ≤ m) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) : level x q i ≤ level x q j := by
  rcases Nat.lt_or_ge j m with hjm | hjm
  · rw [level_of_lt _ _ _ hjm, level_of_lt _ _ _ (by omega)]; exact h i j hij hjm
  · have hjm' : j = m := le_antisymm hj hjm
    rw [hjm', level_m]
    rcases Nat.lt_or_ge i m with him | him
    · rw [level_of_lt _ _ _ him]
      have := h i (m - 1) (by omega) (by omega); linarith
    · have : i = m := le_antisymm (hij.trans hj) him
      rw [this, level_m]

lemma Inv.level_nonneg {x : PerishBaseStock.Lifetime.State m} (h : Inv x) {q : ℝ} (hq : 0 ≤ q)
    (i : ℕ) : 0 ≤ level x q i := by
  unfold level; split_ifs
  · exact h.nonneg i
  · linarith [h.nonneg (m - 1)]

lemma Inv.outdate_nonneg {x : PerishBaseStock.Lifetime.State m} (h : Inv x) {q : ℝ}
    (hq : 0 ≤ q) (d : ℝ) : 0 ≤ outdate x q d :=
  le_min (le_max_right _ _) (h.level_nonneg hq 1)

lemma Inv.step {x : PerishBaseStock.Lifetime.State m} (h : Inv x) {q : ℝ} (hq : 0 ≤ q)
    (hm : 1 ≤ m) (d : ℝ) : Inv (lifoStep x q d) := by
  have hmono := fun {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) => h.level_mono hq hm hij hj
  intro i j hij hj
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    rw [cum_zero]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0; rw [cum_zero]
    · rw [cum_lifoStep _ _ _ _ hj0 hj, sub_nonneg]
      unfold outdate
      exact min_le_min_left _ (hmono (by omega) (by omega))
  · rw [cum_lifoStep _ _ _ _ hi0 (by omega), cum_lifoStep _ _ _ _ (by omega) hj]
    exact sub_le_sub_right (min_le_min_left _ (hmono (by omega) (by omega))) _

lemma inv_run (π : PerishBaseStock.Lifetime.Policy m) (hm : 1 ≤ m)
    (d : CappedBaseStock.DemandPath) : ∀ t, Inv (run π d t) := by
  intro t
  induction t with
  | zero => intro i j _ _; simp [run, cum_empty]
  | succ t ih => exact ih.step (NNReal.coe_nonneg _) hm _

/-! ### Base-stock specifics -/

lemma bs_upTo (S : ℝ≥0) {x : PerishBaseStock.Lifetime.State m} (h : Inv x)
    (hS : cum x (m - 1) ≤ S) :
    level x ((baseStock m S).φ 0 x : ℝ) m = S := by
  rw [level_m]
  simp only [baseStock]
  rw [Real.coe_toNNReal _ (by linarith)]
  ring

lemma bs_top (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) :
    ∀ t, cum (run (baseStock m S) d t) (m - 1) ≤ S := by
  intro t
  induction t with
  | zero => simp [run, cum_empty]
  | succ t ih =>
    have hinv := inv_run (baseStock m S) hm d t
    rcases Nat.lt_or_ge 1 m with h2 | h1
    · simp only [run]
      rw [cum_lifoStep _ _ _ _ (by omega) (by omega)]
      have hq : (0 : ℝ) ≤ ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) :=
        NNReal.coe_nonneg _
      have h1 := hinv.outdate_nonneg hq (d t : ℝ)
      have h2 : min (leftover (run (baseStock m S) d t)
          ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) (d t))
          (level (run (baseStock m S) d t) ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ)
            (m - 1 + 1)) ≤ S := by
        refine (min_le_left _ _).trans ?_
        unfold leftover
        have := bs_upTo S hinv ih
        simp only [baseStock] at this ⊢
        rw [this]
        exact max_le (by linarith [(d t).2]) S.2
      linarith
    · rw [show m - 1 = 0 by omega, cum_zero]; exact S.2

/-- Under `π_S` the order-up-to level is `S` in every period. -/
lemma bs_level_m (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    level (run (baseStock m S) d t) ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) m = S :=
  bs_upTo S (inv_run _ hm d t) (bs_top S hm d t)

/-- Shorthand for the base-stock outdating and levels. -/
noncomputable abbrev o (m : ℕ) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  outdated (baseStock m S) d t

noncomputable abbrev u (m : ℕ) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t i : ℕ) : ℝ :=
  level (run (baseStock m S) d t) ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) i

lemma bs_leftover (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    leftover (run (baseStock m S) d t) ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) (d t)
      = max ((S : ℝ) - d t) 0 := by
  unfold leftover; rw [bs_level_m S hm d t]

/-- One-step recursion `u_{s+1, j-1} = min(L_s, u_{s,j}) - o_s`. -/
lemma u_step (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (s j : ℕ) (h1 : 1 ≤ j)
    (hj : j ≤ m) :
    u m S d (s + 1) (j - 1) = min (max ((S : ℝ) - d s) 0) (u m S d s j) - o m S d s := by
  have := key (run (baseStock m S) d s) ((baseStock m S).φ s (run (baseStock m S) d s) : ℝ)
    (d s) ((baseStock m S).φ (s + 1) (run (baseStock m S) d (s + 1)) : ℝ) j h1 hj
  rw [bs_leftover S hm d s] at this
  simp only [u, o, outdated]
  rw [← this]
  simp [run]

lemma inf'_sub {s : Finset ℕ} (H : s.Nonempty) (f : ℕ → ℝ) (c : ℝ) :
    s.inf' H f - c = s.inf' H (fun i => f i - c) := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ fun i hi => sub_le_sub_right (Finset.inf'_le _ hi) _
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' H f
    rw [he]; exact Finset.inf'_le (fun i => f i - c) hi

lemma inf'_range_succ (k : ℕ) (H1 : (Finset.range (k + 1)).Nonempty)
    (H2 : (Finset.range k).Nonempty) (f : ℕ → ℝ) :
    (Finset.range (k + 1)).inf' H1 f = min (f k) ((Finset.range k).inf' H2 f) := by
  apply le_antisymm
  · exact le_min (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_self k)))
      (Finset.le_inf' _ _ fun i hi =>
        Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hi))))
  · refine Finset.le_inf' _ _ fun i hi => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hi) with h | h
    · exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 h))
    · rw [h]; exact min_le_left _ _

/-- The window formula: for `1 ≤ k ≤ m`,
`u_{t+k, m-k} = min_{i<k} (L_{t+i} - Σ_{j=t+i}^{t+k-1} o_j)`. -/
lemma window (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    ∀ k (hk : 1 ≤ k), k ≤ m → u m S d (t + k) (m - k) =
      (Finset.range k).inf' (Finset.nonempty_range_iff.mpr (by omega))
        (fun i => max ((S : ℝ) - d (t + i)) 0 - ∑ j ∈ Finset.Ico (t + i) (t + k), o m S d j) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    have h := u_step S hm d t m hm le_rfl
    simp only [u] at h
    rw [bs_level_m S hm d t, min_eq_left (max_le (by linarith [(d t).2]) (NNReal.coe_nonneg S))] at h
    simp only [u, Finset.range_one, Finset.inf'_singleton, add_zero]
    rw [h, Finset.sum_Ico_succ_top (le_refl t), Finset.Ico_self, Finset.sum_empty, zero_add]
  | succ k hk ih =>
    intro hk1
    have h := u_step S hm d (t + k) (m - k) (by omega) (by omega)
    rw [show m - k - 1 = m - (k + 1) by omega, ih (by omega)] at h
    rw [show t + (k + 1) = t + k + 1 by ring, h]
    rw [inf'_range_succ k _ (Finset.nonempty_range_iff.mpr (by omega)), ← min_sub_sub_right, inf'_sub]
    congr 1
    · rw [Finset.sum_Ico_succ_top (by omega), Finset.Ico_self, Finset.sum_empty, zero_add]
    · refine Finset.inf'_congr _ rfl fun i hi => ?_
      have : t + i ≤ t + k := by have := Finset.mem_range.mp hi; omega
      rw [Finset.sum_Ico_succ_top this]; ring

end L5D

namespace L5D
open PerishBaseStock.Lifo

theorem ec18 (m : ℕ) (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    outdated (baseStock m S) d (t + m - 1) =
      (Finset.range m).inf' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun i => max ((S : ℝ) - d (t + i)) 0 -
          ∑ j ∈ Finset.Ico (t + i) (t + m - 1), outdated (baseStock m S) d j) := by
  have hw := window S hm d t m hm le_rfl
  have h0 : u m S d (t + m) (m - m) = 0 := by
    simp only [u, Nat.sub_self]
    rw [level_of_lt _ _ _ (by omega), cum_zero]
  rw [h0] at hw
  have hsplit : ∀ i ∈ Finset.range m, max ((S : ℝ) - d (t + i)) 0 -
      ∑ j ∈ Finset.Ico (t + i) (t + m), o m S d j =
      (max ((S : ℝ) - d (t + i)) 0 -
        ∑ j ∈ Finset.Ico (t + i) (t + m - 1), outdated (baseStock m S) d j)
        - outdated (baseStock m S) d (t + m - 1) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [show t + m = t + m - 1 + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
    simp only [o, show t + m - 1 + 1 - 1 = t + m - 1 by omega]
    ring
  rw [Finset.inf'_congr _ rfl hsplit, ← inf'_sub] at hw
  linarith

end L5D


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable {m : ℕ}

lemma cont_cum (i : ℕ) : Continuous (fun x : PerishBaseStock.Lifetime.State m => cum x i) := by
  unfold cum; split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma cont_level (i : ℕ) :
    Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ => level p.1 p.2 i) := by
  unfold level; split_ifs
  · exact (cont_cum i).comp continuous_fst
  · exact ((cont_cum (m - 1)).comp continuous_fst).add continuous_snd

lemma cont_leftover :
    Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ × ℝ => leftover p.1 p.2.1 p.2.2) := by
  unfold leftover
  exact (((cont_level m).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).sub
    (continuous_snd.comp continuous_snd)).max continuous_const

lemma cont_outdate :
    Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ × ℝ => outdate p.1 p.2.1 p.2.2) := by
  unfold outdate
  exact cont_leftover.min
    ((cont_level 1).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))

lemma cont_lifoStep :
    Continuous (fun p : PerishBaseStock.Lifetime.State m × ℝ × ℝ => lifoStep p.1 p.2.1 p.2.2) := by
  refine continuous_pi fun j => ?_
  simp only [lifoStep]
  exact (cont_leftover.min ((cont_level (j.val + 2)).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))).sub cont_outdate

lemma meas_run (π : PerishBaseStock.Lifetime.Policy m) (t : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => run π d t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have h1 : Measurable (fun d : CappedBaseStock.DemandPath =>
        ((run π d t, ((π.φ t (run π d t) : ℝ≥0) : ℝ), ((d t : ℝ≥0) : ℝ)) :
          PerishBaseStock.Lifetime.State m × ℝ × ℝ)) :=
      ih.prodMk ((measurable_coe_nnreal_real.comp ((π.measurable_φ t).comp ih)).prodMk
        (measurable_coe_nnreal_real.comp (measurable_pi_apply t)))
    exact cont_lifoStep.measurable.comp h1

lemma meas_outdated (π : PerishBaseStock.Lifetime.Policy m) (t : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => outdated π d t) := by
  have h1 : Measurable (fun d : CappedBaseStock.DemandPath =>
      ((run π d t, ((π.φ t (run π d t) : ℝ≥0) : ℝ), ((d t : ℝ≥0) : ℝ)) :
        PerishBaseStock.Lifetime.State m × ℝ × ℝ)) :=
    (meas_run π t).prodMk ((measurable_coe_nnreal_real.comp
      ((π.measurable_φ t).comp (meas_run π t))).prodMk
      (measurable_coe_nnreal_real.comp (measurable_pi_apply t)))
  exact cont_outdate.measurable.comp h1

lemma meas_orderUpTo (π : PerishBaseStock.Lifetime.Policy m) (t : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => orderUpTo π d t) := by
  have h1 : Measurable (fun d : CappedBaseStock.DemandPath =>
      ((run π d t, ((π.φ t (run π d t) : ℝ≥0) : ℝ)) : PerishBaseStock.Lifetime.State m × ℝ)) :=
    (meas_run π t).prodMk (measurable_coe_nnreal_real.comp
      ((π.measurable_φ t).comp (meas_run π t)))
  exact (cont_level m).measurable.comp h1

/-! ### Pathwise bounds for `π_S` -/

lemma o_nonneg (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    0 ≤ o m S d t :=
  (inv_run (baseStock m S) hm d t).outdate_nonneg (NNReal.coe_nonneg _) _

lemma o_le (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    o m S d t ≤ max ((S : ℝ) - d t) 0 := by
  simp only [o, outdated, outdate]
  rw [bs_leftover S hm d t]; exact min_le_left _ _

lemma o_le_S (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    o m S d t ≤ S :=
  (o_le S hm d t).trans (max_le (by linarith [(d t).2]) S.2)

lemma window_m (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    (Finset.range m).inf' (Finset.nonempty_range_iff.mpr (by omega))
        (fun i => max ((S : ℝ) - d (t + i)) 0 - ∑ j ∈ Finset.Ico (t + i) (t + m), o m S d j) = 0 := by
  rw [← window S hm d t m hm le_rfl]
  simp only [u, Nat.sub_self]
  rw [level_of_lt _ _ _ (by omega), cum_zero]

/-- `Σ_{j=t}^{t+m-1} o_j ≤ (S - D_t)⁺`. -/
lemma sum_o_le (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    ∑ j ∈ Finset.Ico t (t + m), o m S d j ≤ max ((S : ℝ) - d t) 0 := by
  have h := window_m S hm d t
  have := Finset.inf'_le (fun i => max ((S : ℝ) - d (t + i)) 0 -
      ∑ j ∈ Finset.Ico (t + i) (t + m), o m S d j) (Finset.mem_range.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hm))
  rw [h] at this
  simp only [add_zero] at this
  linarith

/-- `Σ_{j=t}^{t+m-1} o_j ≥ (S - max_{i<m} D_{t+i})⁺`. -/
lemma sum_o_ge (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    max ((S : ℝ) - ((Finset.range m).sup (fun i => d (t + i)) : ℝ≥0)) 0 ≤
      ∑ j ∈ Finset.Ico t (t + m), o m S d j := by
  have h := window_m S hm d t
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_range_iff.mpr (show m ≠ 0 by omega))
    (fun i => max ((S : ℝ) - d (t + i)) 0 - ∑ j ∈ Finset.Ico (t + i) (t + m), o m S d j)
  rw [h] at he
  have hi' := Finset.mem_range.1 hi
  have hsub : ∑ j ∈ Finset.Ico (t + i) (t + m), o m S d j ≤ ∑ j ∈ Finset.Ico t (t + m), o m S d j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (by omega) le_rfl)
      (fun j _ _ => o_nonneg S hm d j)
  have hmax : ((d (t + i) : ℝ≥0) : ℝ) ≤ ((Finset.range m).sup (fun i => d (t + i)) : ℝ≥0) := by
    exact_mod_cast Finset.le_sup (f := fun i => d (t + i)) hi
  have : max ((S : ℝ) - ((Finset.range m).sup (fun i => d (t + i)) : ℝ≥0)) 0 ≤
      max ((S : ℝ) - d (t + i)) 0 := max_le_max (by linarith) le_rfl
  linarith

end L5D


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw)

lemma law_shift (t : ℕ) :
    (CappedBaseStock.demandPathLaw P).map (fun d i => d (t + i)) = CappedBaseStock.demandPathLaw P := by
  unfold CappedBaseStock.demandPathLaw
  exact Measure.map_infinitePi_infinitePi_of_inj (add_right_injective t)

lemma meas_shift (t : ℕ) : Measurable (fun (d : CappedBaseStock.DemandPath) (i : ℕ) => d (t + i)) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

variable {m : ℕ}

lemma int_o (S : ℝ≥0) (hm : 1 ≤ m) (t : ℕ) :
    Integrable (fun d => o m S d t) (CappedBaseStock.demandPathLaw P) := by
  refine Integrable.mono' (integrable_const (S : ℝ)) (meas_outdated _ t).aestronglyMeasurable
    (Eventually.of_forall fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (o_nonneg S hm d t)]
  exact o_le_S S hm d t

lemma lint_o (S : ℝ≥0) (hm : 1 ≤ m) (t : ℕ) :
    ∫⁻ d, ENNReal.ofReal (o m S d t) ∂CappedBaseStock.demandPathLaw P =
      ENNReal.ofReal (∫ d, o m S d t ∂CappedBaseStock.demandPathLaw P) :=
  (ofReal_integral_eq_lintegral_ofReal (int_o P S hm t)
    (Eventually.of_forall fun d => o_nonneg S hm d t)).symm

lemma E_nonneg (S : ℝ≥0) (hm : 1 ≤ m) (t : ℕ) :
    0 ≤ ∫ d, o m S d t ∂CappedBaseStock.demandPathLaw P :=
  integral_nonneg fun d => o_nonneg S hm d t

lemma EHmax_eq (hm : 1 ≤ m) (S : ℝ≥0) (t : ℕ) :
    expectedHolding (maxLaw P (m - 1)) S =
      ∫ d, max ((S : ℝ) - ((Finset.range m).sup (fun i => d (t + i)) : ℝ≥0)) 0
        ∂CappedBaseStock.demandPathLaw P := by
  have hf : Measurable (fun x : ℝ≥0 => max ((S : ℝ) - x) 0) := by fun_prop
  unfold expectedHolding maxLaw
  rw [integral_map (L5H.meas_maxfun (m - 1)).aemeasurable hf.aestronglyMeasurable]
  rw [show m - 1 + 1 = m by omega]
  conv_lhs => rw [← law_shift P t]
  have hg : Measurable (fun d : CappedBaseStock.DemandPath => (Finset.range m).sup d) := by
    have := L5H.meas_maxfun (m - 1); rwa [show m - 1 + 1 = m by omega] at this
  exact integral_map (f := fun x : CappedBaseStock.DemandPath =>
    max ((S : ℝ) - ((Finset.range m).sup x : ℝ≥0)) 0) (meas_shift t).aemeasurable
    (hf.comp hg).aestronglyMeasurable

/-- (EC.19) in real form. -/
lemma ec19_real (hm : 1 ≤ m) (S : ℝ≥0) (t : ℕ) :
    expectedHolding (maxLaw P (m - 1)) S ≤
      ∑ j ∈ Finset.Ico t (t + m), ∫ d, o m S d j ∂CappedBaseStock.demandPathLaw P := by
  rw [EHmax_eq P hm S t, ← integral_finsetSum _ fun j _ => int_o P S hm j]
  have hg : Measurable (fun d : CappedBaseStock.DemandPath =>
      (Finset.range m).sup (fun i => d (t + i))) := by
    have := (L5H.meas_maxfun (m - 1)).comp (meas_shift t)
    rw [show m - 1 + 1 = m by omega] at this; exact this
  refine integral_mono ?_ (integrable_finsetSum _ fun j _ => int_o P S hm j)
    fun d => sum_o_ge S hm d t
  have hf : Measurable (fun x : ℝ≥0 => max ((S : ℝ) - x) 0) := by fun_prop
  refine Integrable.mono' (integrable_const (S : ℝ)) (hf.comp hg).aestronglyMeasurable
    (Eventually.of_forall fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [NNReal.coe_nonneg ((Finset.range m).sup (fun i => d (t + i)))]) S.2

theorem ec19 (hm : 1 ≤ m) (S : ℝ≥0) (t : ℕ) :
    ENNReal.ofReal (expectedHolding (maxLaw P (m - 1)) S) ≤
      ∑ j ∈ Finset.Ico t (t + m),
        ∫⁻ d, ENNReal.ofReal (outdated (baseStock m S) d j) ∂CappedBaseStock.demandPathLaw P := by
  have : ∀ j ∈ Finset.Ico t (t + m),
      ∫⁻ d, ENNReal.ofReal (outdated (baseStock m S) d j) ∂CappedBaseStock.demandPathLaw P =
        ENNReal.ofReal (∫ d, o m S d j ∂CappedBaseStock.demandPathLaw P) :=
    fun j _ => lint_o P S hm j
  rw [Finset.sum_congr rfl this, ← ENNReal.ofReal_sum_of_nonneg fun j _ => E_nonneg P S hm j]
  exact ENNReal.ofReal_le_ofReal (ec19_real P hm S t)

end L5D


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw) {m : ℕ}

lemma int_coord_hold (S : ℝ≥0) (t : ℕ) :
    Integrable (fun d : CappedBaseStock.DemandPath => max ((S : ℝ) - d t) 0)
      (CappedBaseStock.demandPathLaw P) := by
  have := L5H.int_hold P.law S
  rw [L5H.law_eq_map P t] at this
  exact this.comp_measurable (measurable_pi_apply t)

lemma int_coord_short (S : ℝ≥0) (t : ℕ) :
    Integrable (fun d : CappedBaseStock.DemandPath => max ((d t : ℝ) - S) 0)
      (CappedBaseStock.demandPathLaw P) := by
  have := L5H.int_short P S
  rw [L5H.law_eq_map P t] at this
  exact this.comp_measurable (measurable_pi_apply t)

lemma integral_coord_hold (S : ℝ≥0) (t : ℕ) :
    ∫ d, max ((S : ℝ) - d t) 0 ∂CappedBaseStock.demandPathLaw P = expectedHolding P.law S := by
  unfold expectedHolding
  conv_rhs => rw [L5H.law_eq_map P t]
  rw [integral_map (measurable_pi_apply t).aemeasurable (by fun_prop)]

lemma integral_coord_short (S : ℝ≥0) (t : ℕ) :
    ∫ d, max ((d t : ℝ) - S) 0 ∂CappedBaseStock.demandPathLaw P = expectedShortfall P.law S := by
  unfold expectedShortfall
  conv_rhs => rw [L5H.law_eq_map P t]
  rw [integral_map (measurable_pi_apply t).aemeasurable (by fun_prop)]

/-- Expected period cost of `π_S`. -/
lemma lint_periodCost (c : Params) (hc : c.Standing) (S : ℝ≥0) (t : ℕ) :
    ∫⁻ d, periodCost c (baseStock c.m S) d t ∂CappedBaseStock.demandPathLaw P =
      ENNReal.ofReal (backorderCost P.law c.h c.p S +
        c.θ * ∫ d, o c.m S d t ∂CappedBaseStock.demandPathLaw P) := by
  have hm := hc.one_le_m
  have hpt : ∀ d, periodCost c (baseStock c.m S) d t = ENNReal.ofReal
      (c.h * max ((S : ℝ) - d t) 0 + c.p * max ((d t : ℝ) - S) 0 + c.θ * o c.m S d t) := by
    intro d
    unfold periodCost
    have hU : orderUpTo (baseStock c.m S) d t = S := bs_level_m S hm d t
    have a1 : 0 ≤ c.h * max ((S : ℝ) - d t) 0 := mul_nonneg hc.h_pos.le (le_max_right _ _)
    have a2 : 0 ≤ c.p * max ((d t : ℝ) - S) 0 := mul_nonneg hc.p_pos.le (le_max_right _ _)
    have a3 : 0 ≤ c.θ * o c.m S d t := mul_nonneg hc.θ_nonneg (o_nonneg S hm d t)
    rw [hU, ENNReal.ofReal_add (add_nonneg a1 a2) a3, ENNReal.ofReal_add a1 a2]
  simp_rw [hpt]
  have i1 := (int_coord_hold P S t).const_mul c.h
  have i2 := (int_coord_short P S t).const_mul c.p
  have i3 := (int_o P S hm t).const_mul c.θ
  have hint : Integrable (fun d : CappedBaseStock.DemandPath => c.h * max ((S : ℝ) - d t) 0 +
      c.p * max ((d t : ℝ) - S) 0 + c.θ * o c.m S d t) (CappedBaseStock.demandPathLaw P) :=
    (i1.add i2).add i3
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun d => add_nonneg (add_nonneg
      (mul_nonneg hc.h_pos.le (le_max_right _ _)) (mul_nonneg hc.p_pos.le (le_max_right _ _)))
      (mul_nonneg hc.θ_nonneg (o_nonneg S hm d t)))]
  congr 1
  have e1 : ∫ x, (c.h * max ((S : ℝ) - x t) 0 + c.p * max ((x t : ℝ) - S) 0 + c.θ * o c.m S x t)
      ∂CappedBaseStock.demandPathLaw P = ∫ x, (c.h * max ((S : ℝ) - x t) 0 +
        c.p * max ((x t : ℝ) - S) 0) ∂CappedBaseStock.demandPathLaw P +
        ∫ x, c.θ * o c.m S x t ∂CappedBaseStock.demandPathLaw P := integral_add (i1.add i2) i3
  have e2 : ∫ x, (c.h * max ((S : ℝ) - x t) 0 + c.p * max ((x t : ℝ) - S) 0)
      ∂CappedBaseStock.demandPathLaw P = ∫ x, c.h * max ((S : ℝ) - x t) 0
        ∂CappedBaseStock.demandPathLaw P + ∫ x, c.p * max ((x t : ℝ) - S) 0
        ∂CappedBaseStock.demandPathLaw P := integral_add i1 i2
  rw [e1, e2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_coord_hold, integral_coord_short]
  rfl

lemma cesaro_ofReal (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (T : ℕ) :
    (∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (a t)) / ((T : ℝ≥0∞) + 1) =
      ENNReal.ofReal ((∑ t ∈ Finset.range (T + 1), a t) / (T + 1)) := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => ha t,
    ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp

/-- `C^{LIFO}(S)` as a limsup of real Cesàro averages. -/
lemma bsCost_eq (c : Params) (hc : c.Standing) (S : ℝ≥0) :
    baseStockCost P c S = limsup (fun T : ℕ => ENNReal.ofReal
      ((∑ t ∈ Finset.range (T + 1), (backorderCost P.law c.h c.p S +
        c.θ * ∫ d, o c.m S d t ∂CappedBaseStock.demandPathLaw P)) / (T + 1))) atTop := by
  unfold baseStockCost policyCost
  congr 1
  funext T
  simp_rw [lint_periodCost P c hc S]
  apply cesaro_ofReal
  intro t
  have h1 : 0 ≤ backorderCost P.law c.h c.p S :=
    add_nonneg (mul_nonneg hc.h_pos.le (L5H.EH_nonneg _ _)) (mul_nonneg hc.p_pos.le (L5H.ES_nonneg _ _))
  exact add_nonneg h1 (mul_nonneg hc.θ_nonneg (E_nonneg P S hc.one_le_m t))

/-- Pathwise: `m Σ_{j≤T} o_j ≤ Σ_{t≤T} (S-D_t)⁺ + m² S`. -/
lemma sum_o_upper (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (T : ℕ) :
    (m : ℝ) * ∑ j ∈ Finset.range (T + 1), o m S d j ≤
      ∑ t ∈ Finset.range (T + 1), max ((S : ℝ) - d t) 0 + (m : ℝ) * m * S := by
  have hS := NNReal.coe_nonneg S
  have hi : ∀ i ∈ Finset.range m, ∑ j ∈ Finset.range (T + 1), o m S d j ≤
      i * (S : ℝ) + ∑ t ∈ Finset.range (T + 1), o m S d (t + i) := by
    intro i hi
    have h1 : ∑ j ∈ Finset.range (T + 1), o m S d j ≤ ∑ j ∈ Finset.range (i + (T + 1)), o m S d j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        (fun j _ _ => o_nonneg S hm d j)
    rw [Finset.sum_range_add _ i (T + 1)] at h1
    have h2 : ∑ j ∈ Finset.range i, o m S d j ≤ i * (S : ℝ) := by
      have := Finset.sum_le_sum (s := Finset.range i) fun j _ => o_le_S S hm d j
      simpa using this
    have h3 : ∑ x ∈ Finset.range (T + 1), o m S d (i + x) =
        ∑ t ∈ Finset.range (T + 1), o m S d (t + i) :=
      Finset.sum_congr rfl fun x _ => by rw [add_comm]
    linarith
  have hsum := Finset.sum_le_sum hi
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib] at hsum
  have hw : ∑ i ∈ Finset.range m, ∑ t ∈ Finset.range (T + 1), o m S d (t + i) ≤
      ∑ t ∈ Finset.range (T + 1), max ((S : ℝ) - d t) 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun t _ => ?_
    have := sum_o_le S hm d t
    rw [Finset.sum_Ico_eq_sum_range] at this
    simpa [add_comm] using this
  have hi2 : ∑ i ∈ Finset.range m, (i : ℝ) * S ≤ (m : ℝ) * m * S := by
    have : ∀ i ∈ Finset.range m, (i : ℝ) * S ≤ m * S := fun i hi =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.1 hi).le) hS
    have := Finset.sum_le_sum this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  linarith

end L5D


open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable {m : ℕ}

/-- `U_{s,i}` for a general policy. -/
noncomputable abbrev U (π : PerishBaseStock.Lifetime.Policy m) (d : CappedBaseStock.DemandPath)
    (s i : ℕ) : ℝ :=
  level (run π d s) (π.φ s (run π d s) : ℝ) i

lemma U_step (π : PerishBaseStock.Lifetime.Policy m) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath)
    (s j : ℕ) (h1 : 1 ≤ j) (hj : j ≤ m) :
    U π d s j ≤ U π d (s + 1) (j - 1) + outdated π d s + d s := by
  have hk := key (run π d s) (π.φ s (run π d s) : ℝ) (d s)
    (π.φ (s + 1) (run π d (s + 1)) : ℝ) j h1 hj
  have hinv := inv_run π hm d s
  have hq : (0 : ℝ) ≤ (π.φ s (run π d s) : ℝ) := NNReal.coe_nonneg _
  have hmono := hinv.level_mono hq hm hj le_rfl
  have hd := (d s).2
  have hr : run π d (s + 1) = lifoStep (run π d s) (π.φ s (run π d s) : ℝ) (d s) := rfl
  simp only [U, outdated]
  rw [hr]
  rw [hr] at hk
  rw [hk]
  unfold leftover
  rcases le_total (max (level (run π d s) (π.φ s (run π d s) : ℝ) m - d s) 0)
    (level (run π d s) (π.φ s (run π d s) : ℝ) j) with h | h
  · rw [min_eq_left h]
    have := le_max_left (level (run π d s) (π.φ s (run π d s) : ℝ) m - d s) 0
    linarith
  · rw [min_eq_right h]; linarith

/-- (15): `Σ_{j=t}^{t+m-1} o_j ≥ x_{t,m} - Σ_{i=t}^{t+m-1} D_i`, for any policy. -/
lemma sum_o_ge_gen (π : PerishBaseStock.Lifetime.Policy m) (hm : 1 ≤ m)
    (d : CappedBaseStock.DemandPath) (t : ℕ) :
    orderUpTo π d t - ∑ i ∈ Finset.range m, (d (t + i) : ℝ) ≤
      ∑ i ∈ Finset.range m, outdated π d (t + i) := by
  have claim : ∀ k, k ≤ m → U π d t m ≤ U π d (t + k) (m - k) +
      ∑ i ∈ Finset.range k, (outdated π d (t + i) + d (t + i)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := U_step π hm d (t + k) (m - k) (by omega) (by omega)
      rw [show m - k - 1 = m - (k + 1) by omega, show t + k + 1 = t + (k + 1) by ring] at h2
      rw [Finset.sum_range_succ]
      linarith
  have h := claim m le_rfl
  have h0 : U π d (t + m) (m - m) = 0 := by
    simp only [U, Nat.sub_self]; rw [level_of_lt _ _ _ (by omega), cum_zero]
  rw [h0, zero_add, Finset.sum_add_distrib] at h
  simp only [orderUpTo]
  linarith

/-- Run depends only on the past. -/
lemma run_congr (π : PerishBaseStock.Lifetime.Policy m) (d d' : CappedBaseStock.DemandPath) :
    ∀ s, (∀ i < s, d i = d' i) → run π d s = run π d' s := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro h
    have := ih (fun i hi => h i (by omega))
    simp only [run, this, h s (by omega)]

end L5D


open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw) {m : ℕ}

lemma EHsum_eq (hm : 1 ≤ m) (S : ℝ≥0) (t : ℕ) :
    expectedHolding (leadTimeLaw P (m - 1)) S =
      ∫ d, max ((S : ℝ) - ∑ i ∈ Finset.range m, (d (t + i) : ℝ)) 0
        ∂CappedBaseStock.demandPathLaw P := by
  have hf : Measurable (fun x : ℝ≥0 => max ((S : ℝ) - x) 0) := by fun_prop
  unfold expectedHolding leadTimeLaw
  rw [integral_map (L5H.meas_sumfun (m - 1)).aemeasurable hf.aestronglyMeasurable]
  rw [show m - 1 + 1 = m by omega]
  conv_lhs => rw [← law_shift P t]
  have hg : Measurable (fun d : CappedBaseStock.DemandPath => ∑ i ∈ Finset.range m, d i) := by
    have := L5H.meas_sumfun (m - 1); rwa [show m - 1 + 1 = m by omega] at this
  rw [integral_map (f := fun x : CappedBaseStock.DemandPath =>
    max ((S : ℝ) - ((∑ i ∈ Finset.range m, x i : ℝ≥0) : ℝ)) 0) (meas_shift t).aemeasurable
    (hf.comp hg).aestronglyMeasurable]
  simp [NNReal.coe_sum]

lemma int_sum_hold (hm : 1 ≤ m) (S : ℝ≥0) (t : ℕ) :
    Integrable (fun d : CappedBaseStock.DemandPath =>
      max ((S : ℝ) - ∑ i ∈ Finset.range m, (d (t + i) : ℝ)) 0) (CappedBaseStock.demandPathLaw P) := by
  refine Integrable.mono' (integrable_const (S : ℝ)) ?_ (Eventually.of_forall fun d => ?_)
  · have : Measurable (fun d : CappedBaseStock.DemandPath =>
        max ((S : ℝ) - ∑ i ∈ Finset.range m, (d (t + i) : ℝ)) 0) := by
      refine Measurable.max (measurable_const.sub ?_) measurable_const
      exact Finset.measurable_sum _ fun i _ =>
        measurable_coe_nnreal_real.comp (measurable_pi_apply _)
    exact this.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have : 0 ≤ ∑ i ∈ Finset.range m, (d (t + i) : ℝ) :=
      Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
    exact max_le (by linarith) S.2

/-- For a fixed level `s`, the expected one-period lower-bound cost is `C̃(s)`. -/
lemma lint_g_fixed (c : Params) (hc : c.Standing) (s : ℝ≥0) (t : ℕ) :
    ∫⁻ d, ENNReal.ofReal (c.h * max ((s : ℝ) - d t) 0 + c.p * max ((d t : ℝ) - s) 0 +
        c.θ / c.m * max ((s : ℝ) - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0)
        ∂CappedBaseStock.demandPathLaw P = ENNReal.ofReal (tildeC P c s) := by
  have hm := hc.one_le_m
  have i1 := (int_coord_hold P s t).const_mul c.h
  have i2 := (int_coord_short P s t).const_mul c.p
  have i3 := (int_sum_hold P hm s t).const_mul (c.θ / c.m)
  have hint : Integrable (fun d : CappedBaseStock.DemandPath => c.h * max ((s : ℝ) - d t) 0 +
      c.p * max ((d t : ℝ) - s) 0 +
        c.θ / c.m * max ((s : ℝ) - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0)
      (CappedBaseStock.demandPathLaw P) := (i1.add i2).add i3
  have hθm : 0 ≤ c.θ / c.m := div_nonneg hc.θ_nonneg (Nat.cast_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun d => add_nonneg (add_nonneg
      (mul_nonneg hc.h_pos.le (le_max_right _ _)) (mul_nonneg hc.p_pos.le (le_max_right _ _)))
      (mul_nonneg hθm (le_max_right _ _)))]
  congr 1
  have e1 : ∫ x, (c.h * max ((s : ℝ) - x t) 0 + c.p * max ((x t : ℝ) - s) 0 +
      c.θ / c.m * max ((s : ℝ) - ∑ i ∈ Finset.range c.m, (x (t + i) : ℝ)) 0)
      ∂CappedBaseStock.demandPathLaw P = ∫ x, (c.h * max ((s : ℝ) - x t) 0 +
        c.p * max ((x t : ℝ) - s) 0) ∂CappedBaseStock.demandPathLaw P +
        ∫ x, c.θ / c.m * max ((s : ℝ) - ∑ i ∈ Finset.range c.m, (x (t + i) : ℝ)) 0
          ∂CappedBaseStock.demandPathLaw P := integral_add (i1.add i2) i3
  have e2 : ∫ x, (c.h * max ((s : ℝ) - x t) 0 + c.p * max ((x t : ℝ) - s) 0)
      ∂CappedBaseStock.demandPathLaw P = ∫ x, c.h * max ((s : ℝ) - x t) 0
        ∂CappedBaseStock.demandPathLaw P + ∫ x, c.p * max ((x t : ℝ) - s) 0
        ∂CappedBaseStock.demandPathLaw P := integral_add i1 i2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul, integral_coord_hold,
    integral_coord_short, ← EHsum_eq P hm s t]
  rfl

end L5D


open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw)

/-- Completion of a finite past by zeros. -/
noncomputable def ext (t : ℕ) (a : (i : Finset.range t) → ℝ≥0) : CappedBaseStock.DemandPath :=
  fun i => if h : i ∈ Finset.range t then a ⟨i, h⟩ else 0

lemma meas_ext (t : ℕ) : Measurable (ext t) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold ext
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The one-period lower-bound integrand as a function of the level and the future demands. -/
noncomputable def gfun (c : Params) (t : ℕ) (x : ℝ) (b : (i : Finset.Ico t (t + c.m)) → ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (c.h * max (x - (if h : t ∈ Finset.Ico t (t + c.m) then (b ⟨t, h⟩ : ℝ) else 0)) 0
    + c.p * max ((if h : t ∈ Finset.Ico t (t + c.m) then (b ⟨t, h⟩ : ℝ) else 0) - x) 0 +
    c.θ / c.m * max (x - ∑ j ∈ (Finset.Ico t (t + c.m)).attach, (b j : ℝ)) 0)

lemma meas_gfun (c : Params) (t : ℕ) :
    Measurable (fun p : ℝ × ((i : Finset.Ico t (t + c.m)) → ℝ≥0) => gfun c t p.1 p.2) := by
  have h2 : Measurable (fun p : ℝ × ((i : Finset.Ico t (t + c.m)) → ℝ≥0) =>
      (if h : t ∈ Finset.Ico t (t + c.m) then ((p.2 ⟨t, h⟩ : ℝ≥0) : ℝ) else 0)) := by
    split_ifs
    · exact measurable_coe_nnreal_real.comp ((measurable_pi_apply _).comp measurable_snd)
    · exact measurable_const
  have h3 : Measurable (fun p : ℝ × ((i : Finset.Ico t (t + c.m)) → ℝ≥0) =>
      ∑ j ∈ (Finset.Ico t (t + c.m)).attach, ((p.2 j : ℝ≥0) : ℝ)) :=
    Finset.measurable_sum _ fun j _ =>
      measurable_coe_nnreal_real.comp ((measurable_pi_apply _).comp measurable_snd)
  unfold gfun
  refine Measurable.ennreal_ofReal ?_
  exact ((measurable_const.mul ((measurable_fst.sub h2).max measurable_const)).add
    (measurable_const.mul ((h2.sub measurable_fst).max measurable_const))).add
    (measurable_const.mul ((measurable_fst.sub h3).max measurable_const))

lemma gfun_eval (c : Params) (hm : 1 ≤ c.m) (t : ℕ) (x : ℝ) (d : CappedBaseStock.DemandPath) :
    gfun c t x (fun i => d i) = ENNReal.ofReal (c.h * max (x - d t) 0 +
      c.p * max ((d t : ℝ) - x) 0 +
      c.θ / c.m * max (x - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0) := by
  have htm : t ∈ Finset.Ico t (t + c.m) := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  have hs : ∑ j ∈ (Finset.Ico t (t + c.m)).attach, ((d j : ℝ≥0) : ℝ) =
      ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ) := by
    rw [Finset.sum_attach (Finset.Ico t (t + c.m)) (fun j => ((d j : ℝ≥0) : ℝ)),
      Finset.sum_Ico_eq_sum_range]
    simp
  unfold gfun
  rw [dif_pos htm, hs]

lemma indep_bound (c : Params) (hc : c.Standing) (St : ℝ≥0) (hSt : IsTildeMinimizer P c St)
    (t : ℕ) (Xp : ((i : Finset.range t) → ℝ≥0) → ℝ) (hXp : Measurable Xp)
    (hXnn : ∀ a, 0 ≤ Xp a) :
    ENNReal.ofReal (tildeC P c St) ≤
      ∫⁻ d, gfun c t (Xp (fun i => d i)) (fun i => d i) ∂CappedBaseStock.demandPathLaw P := by
  have hm := hc.one_le_m
  have hA : Measurable (fun (d : CappedBaseStock.DemandPath) (i : Finset.range t) => d i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hB : Measurable (fun (d : CappedBaseStock.DemandPath) (i : Finset.Ico t (t + c.m)) => d i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hind : IndepFun (fun (d : CappedBaseStock.DemandPath) (i : Finset.range t) => d i)
      (fun (d : CappedBaseStock.DemandPath) (i : Finset.Ico t (t + c.m)) => d i)
      (CappedBaseStock.demandPathLaw P) := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ (x : ℝ≥0) => x)
      (fun _ => measurable_id)
    exact h.indepFun_finset (Finset.range t) (Finset.Ico t (t + c.m))
      (Finset.disjoint_left.2 fun i hi hi' => by
        simp only [Finset.mem_range, Finset.mem_Ico] at hi hi'; omega)
      (fun i => measurable_pi_apply i)
  have hprod := hind.map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable
  set μA := (CappedBaseStock.demandPathLaw P).map
    (fun (d : CappedBaseStock.DemandPath) (i : Finset.range t) => d i)
  set μB := (CappedBaseStock.demandPathLaw P).map
    (fun (d : CappedBaseStock.DemandPath) (i : Finset.Ico t (t + c.m)) => d i)
  have : IsProbabilityMeasure μA := Measure.isProbabilityMeasure_map hA.aemeasurable
  have : IsProbabilityMeasure μB := Measure.isProbabilityMeasure_map hB.aemeasurable
  have hF : Measurable (fun p : ((i : Finset.range t) → ℝ≥0) × ((i : Finset.Ico t (t + c.m)) → ℝ≥0)
      => gfun c t (Xp p.1) p.2) :=
    (meas_gfun c t).comp ((hXp.comp measurable_fst).prodMk measurable_snd)
  have e1 : ∫⁻ d, gfun c t (Xp (fun i => d i)) (fun i => d i) ∂CappedBaseStock.demandPathLaw P =
      ∫⁻ p, gfun c t (Xp p.1) p.2 ∂(μA.prod μB) := by
    rw [← hprod, lintegral_map hF (hA.prodMk hB)]
  rw [e1, lintegral_prod _ hF.aemeasurable]
  have hinner : ∀ a, ENNReal.ofReal (tildeC P c St) ≤ ∫⁻ b, gfun c t (Xp a) b ∂μB := by
    intro a
    have hmeasb : Measurable (fun b => gfun c t (Xp a) b) :=
      (meas_gfun c t).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_map hmeasb hB]
    simp_rw [gfun_eval c hm t]
    have := lint_g_fixed P c hc (Xp a).toNNReal t
    rw [Real.coe_toNNReal _ (hXnn a)] at this
    rw [this]
    exact ENNReal.ofReal_le_ofReal (hSt _)
  calc ENNReal.ofReal (tildeC P c St) = ∫⁻ _a, ENNReal.ofReal (tildeC P c St) ∂μA := by simp
    _ ≤ _ := lintegral_mono hinner

/-- The key expectation bound behind (17). -/
lemma expect_lower (c : Params) (hc : c.Standing) (St : ℝ≥0) (hSt : IsTildeMinimizer P c St)
    (π : PerishBaseStock.Lifetime.Policy c.m) (t : ℕ) :
    ENNReal.ofReal (tildeC P c St) ≤
      ∫⁻ d, ENNReal.ofReal (c.h * max (orderUpTo π d t - d t) 0 +
        c.p * max ((d t : ℝ) - orderUpTo π d t) 0 +
        c.θ / c.m * max (orderUpTo π d t - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0)
        ∂CappedBaseStock.demandPathLaw P := by
  have hm := hc.one_le_m
  have hXp : Measurable (fun a : (i : Finset.range t) → ℝ≥0 => orderUpTo π (ext t a) t) :=
    (meas_orderUpTo π t).comp (meas_ext t)
  have hXnn : ∀ a, 0 ≤ orderUpTo π (ext t a) t := fun a =>
    (inv_run π hm (ext t a) t).level_nonneg (NNReal.coe_nonneg _) _
  have h := indep_bound P c hc St hSt t _ hXp hXnn
  have hX : ∀ d : CappedBaseStock.DemandPath,
      orderUpTo π (ext t (fun i => d i)) t = orderUpTo π d t := by
    intro d
    simp only [orderUpTo]
    rw [run_congr π (ext t (fun i => d i)) d t (fun i hi => by
      simp [ext, Finset.mem_range.2 hi])]
  simp_rw [hX, gfun_eval c hm t] at h
  exact h

end L5D


open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw)

/-- Real one-period lower-bound integrand. -/
noncomputable abbrev gt (c : Params) (π : PerishBaseStock.Lifetime.Policy c.m)
    (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  c.h * max (orderUpTo π d t - d t) 0 + c.p * max ((d t : ℝ) - orderUpTo π d t) 0 +
    c.θ / c.m * max (orderUpTo π d t - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0

/-- Real period cost. -/
noncomputable abbrev ct (c : Params) (π : PerishBaseStock.Lifetime.Policy c.m)
    (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  c.h * max (orderUpTo π d t - d t) 0 + c.p * max ((d t : ℝ) - orderUpTo π d t) 0 +
    c.θ * outdated π d t

lemma periodCost_eq (c : Params) (hc : c.Standing) (π : PerishBaseStock.Lifetime.Policy c.m)
    (d : CappedBaseStock.DemandPath) (t : ℕ) :
    periodCost c π d t = ENNReal.ofReal (ct c π d t) := by
  have a1 : 0 ≤ c.h * max (orderUpTo π d t - d t) 0 := mul_nonneg hc.h_pos.le (le_max_right _ _)
  have a2 : 0 ≤ c.p * max ((d t : ℝ) - orderUpTo π d t) 0 :=
    mul_nonneg hc.p_pos.le (le_max_right _ _)
  have a3 : 0 ≤ c.θ * outdated π d t := mul_nonneg hc.θ_nonneg
    ((inv_run π hc.one_le_m d t).outdate_nonneg (NNReal.coe_nonneg _) _)
  unfold periodCost
  rw [ENNReal.ofReal_add (add_nonneg a1 a2) a3, ENNReal.ofReal_add a1 a2]

lemma sum_gt_le (c : Params) (hc : c.Standing) (π : PerishBaseStock.Lifetime.Policy c.m)
    (d : CappedBaseStock.DemandPath) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), gt c π d t ≤ ∑ t ∈ Finset.range (T + c.m), ct c π d t := by
  have hm := hc.one_le_m
  have hm0 : (0 : ℝ) < c.m := by exact_mod_cast hm
  have onn : ∀ j, 0 ≤ outdated π d j := fun j =>
    (inv_run π hm d j).outdate_nonneg (NNReal.coe_nonneg _) _
  set hp := fun t => c.h * max (orderUpTo π d t - d t) 0 +
    c.p * max ((d t : ℝ) - orderUpTo π d t) 0 with hhp
  have hpnn : ∀ t, 0 ≤ hp t := fun t => add_nonneg (mul_nonneg hc.h_pos.le (le_max_right _ _))
    (mul_nonneg hc.p_pos.le (le_max_right _ _))
  have e1 : ∑ t ∈ Finset.range (T + 1), gt c π d t = ∑ t ∈ Finset.range (T + 1), hp t +
      c.θ / c.m * ∑ t ∈ Finset.range (T + 1),
        max (orderUpTo π d t - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have e2 : ∑ t ∈ Finset.range (T + c.m), ct c π d t = ∑ t ∈ Finset.range (T + c.m), hp t +
      c.θ * ∑ t ∈ Finset.range (T + c.m), outdated π d t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [e1, e2]
  have h1 : ∑ t ∈ Finset.range (T + 1), hp t ≤ ∑ t ∈ Finset.range (T + c.m), hp t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun t _ _ => hpnn t)
  -- window counting
  have h2 : ∑ t ∈ Finset.range (T + 1),
      max (orderUpTo π d t - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0 ≤
      c.m * ∑ t ∈ Finset.range (T + c.m), outdated π d t := by
    have hw : ∀ t, max (orderUpTo π d t - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0 ≤
        ∑ i ∈ Finset.range c.m, outdated π d (t + i) := fun t =>
      max_le (sum_o_ge_gen π hm d t) (Finset.sum_nonneg fun i _ => onn _)
    refine (Finset.sum_le_sum fun t _ => hw t).trans ?_
    rw [Finset.sum_comm]
    have : ∀ i ∈ Finset.range c.m, ∑ t ∈ Finset.range (T + 1), outdated π d (t + i) ≤
        ∑ t ∈ Finset.range (T + c.m), outdated π d t := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have e : ∑ t ∈ Finset.range (T + 1), outdated π d (t + i) =
          ∑ j ∈ Finset.Ico i (i + (T + 1)), outdated π d j := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [add_tsub_cancel_left]
        exact Finset.sum_congr rfl fun t _ => by rw [add_comm]
      rw [e]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => by
          simp only [Finset.mem_Ico] at hj; exact Finset.mem_range.2 (by omega))
        (fun j _ _ => onn j)
    have := Finset.sum_le_sum this
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hθm : 0 ≤ c.θ / c.m := div_nonneg hc.θ_nonneg hm0.le
  have h3 : c.θ / c.m * ∑ t ∈ Finset.range (T + 1),
      max (orderUpTo π d t - ∑ i ∈ Finset.range c.m, (d (t + i) : ℝ)) 0 ≤
      c.θ * ∑ t ∈ Finset.range (T + c.m), outdated π d t := by
    calc _ ≤ c.θ / c.m * (c.m * ∑ t ∈ Finset.range (T + c.m), outdated π d t) :=
          mul_le_mul_of_nonneg_left h2 hθm
      _ = _ := by field_simp
  linarith

lemma meas_ct (c : Params) (π : PerishBaseStock.Lifetime.Policy c.m) (t : ℕ) :
    Measurable (fun d => ct c π d t) := by
  have hX := meas_orderUpTo π t
  have hO := meas_outdated π t
  have hd : Measurable (fun d : CappedBaseStock.DemandPath => ((d t : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp (measurable_pi_apply t)
  exact ((measurable_const.mul ((hX.sub hd).max measurable_const)).add
    (measurable_const.mul ((hd.sub hX).max measurable_const))).add (measurable_const.mul hO)

lemma meas_gt (c : Params) (π : PerishBaseStock.Lifetime.Policy c.m) (t : ℕ) :
    Measurable (fun d => gt c π d t) := by
  have hX := meas_orderUpTo π t
  have hd : Measurable (fun d : CappedBaseStock.DemandPath => ((d t : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp (measurable_pi_apply t)
  have hs : Measurable (fun d : CappedBaseStock.DemandPath =>
      ∑ i ∈ Finset.range c.m, ((d (t + i) : ℝ≥0) : ℝ)) :=
    Finset.measurable_sum _ fun i _ => measurable_coe_nnreal_real.comp (measurable_pi_apply _)
  exact ((measurable_const.mul ((hX.sub hd).max measurable_const)).add
    (measurable_const.mul ((hd.sub hX).max measurable_const))).add
    (measurable_const.mul ((hX.sub hs).max measurable_const))

lemma sum_cost_ge (c : Params) (hc : c.Standing) (St : ℝ≥0) (hSt : IsTildeMinimizer P c St)
    (π : PerishBaseStock.Lifetime.Policy c.m) (T : ℕ) :
    ((T : ℝ≥0∞) + 1) * ENNReal.ofReal (tildeC P c St) ≤
      ∑ t ∈ Finset.range (T + c.m), ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P := by
  have hm := hc.one_le_m
  have gnn : ∀ d t, 0 ≤ gt c π d t := fun d t => add_nonneg (add_nonneg
    (mul_nonneg hc.h_pos.le (le_max_right _ _)) (mul_nonneg hc.p_pos.le (le_max_right _ _)))
    (mul_nonneg (div_nonneg hc.θ_nonneg (Nat.cast_nonneg _)) (le_max_right _ _))
  have cnn : ∀ d t, 0 ≤ ct c π d t := fun d t => add_nonneg (add_nonneg
    (mul_nonneg hc.h_pos.le (le_max_right _ _)) (mul_nonneg hc.p_pos.le (le_max_right _ _)))
    (mul_nonneg hc.θ_nonneg ((inv_run π hm d t).outdate_nonneg (NNReal.coe_nonneg _) _))
  simp_rw [periodCost_eq c hc π]
  rw [← lintegral_finsetSum _ fun t _ => (meas_ct c π t).ennreal_ofReal]
  have hpt : ∀ d, ∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (gt c π d t) ≤
      ∑ t ∈ Finset.range (T + c.m), ENNReal.ofReal (ct c π d t) := by
    intro d
    rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => gnn d t,
      ← ENNReal.ofReal_sum_of_nonneg fun t _ => cnn d t]
    exact ENNReal.ofReal_le_ofReal (sum_gt_le c hc π d T)
  refine le_trans ?_ (lintegral_mono hpt)
  rw [lintegral_finsetSum _ fun t _ => (meas_gt c π t).ennreal_ofReal]
  have : ∀ t ∈ Finset.range (T + 1), ENNReal.ofReal (tildeC P c St) ≤
      ∫⁻ d, ENNReal.ofReal (gt c π d t) ∂CappedBaseStock.demandPathLaw P :=
    fun t _ => expect_lower P c hc St hSt π t
  refine le_trans ?_ (Finset.sum_le_sum this)
  simp

theorem prop2 (c : Params) (hc : c.Standing) (St : ℝ≥0) (hSt : IsTildeMinimizer P c St) :
    ENNReal.ofReal (tildeC P c St) ≤ OPT P c := by
  have hm := hc.one_le_m
  set K := tildeC P c St
  have hK : 0 ≤ K := by
    simp only [K]; unfold tildeC backorderCost
    have := hc.θ_nonneg
    exact add_nonneg (add_nonneg (mul_nonneg hc.h_pos.le (L5H.EH_nonneg _ _))
      (mul_nonneg hc.p_pos.le (L5H.ES_nonneg _ _)))
      (mul_nonneg (div_nonneg this (Nat.cast_nonneg _)) (L5H.EH_nonneg _ _))
  refine le_iInf fun π => ?_
  unfold policyCost
  rw [← limsup_nat_add _ (c.m - 1)]
  have hb : ∀ T : ℕ, ENNReal.ofReal (K * (((T : ℝ) + 1) / ((T : ℝ) + c.m))) ≤
      (∑ t ∈ Finset.range (T + (c.m - 1) + 1),
        ∫⁻ d, periodCost c π d t ∂CappedBaseStock.demandPathLaw P) /
        (((T + (c.m - 1) : ℕ) : ℝ≥0∞) + 1) := by
    intro T
    have hpos : (0 : ℝ) < (T : ℝ) + c.m := by
      have : (1 : ℝ) ≤ c.m := by exact_mod_cast hm
      linarith [(T.cast_nonneg : (0 : ℝ) ≤ T)]
    have hden : (((T + (c.m - 1) : ℕ) : ℝ≥0∞) + 1) = ENNReal.ofReal ((T : ℝ) + c.m) := by
      have e1 : (((T + (c.m - 1) : ℕ) : ℝ≥0∞) + 1) = ((T + c.m : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_succ]; congr 1; omega
      rw [e1, ← ENNReal.ofReal_natCast]; push_cast; rfl
    rw [hden, ENNReal.le_div_iff_mul_le (Or.inl (by simp [hpos])) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (by positivity)]
    rw [show K * (((T : ℝ) + 1) / ((T : ℝ) + c.m)) * ((T : ℝ) + c.m) = ((T : ℝ) + 1) * K by
      field_simp]
    rw [ENNReal.ofReal_mul (by positivity), show T + (c.m - 1) + 1 = T + c.m by omega]
    have := sum_cost_ge P c hc St hSt π T
    convert this using 2
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp
  have hlim : Tendsto (fun T : ℕ => K * (((T : ℝ) + 1) / ((T : ℝ) + c.m))) atTop (𝓝 K) := by
    have h1 : Tendsto (fun T : ℕ => ((T : ℝ) + 1) / ((T : ℝ) + c.m)) atTop (𝓝 1) := by
      have : Tendsto (fun T : ℕ => ((T : ℝ) + 1) / (((T : ℝ) + 1) + ((c.m : ℝ) - 1))) atTop (𝓝 1) := by
        have h := tendsto_natCast_div_add_atTop (𝕜 := ℝ) ((c.m : ℝ) - 1)
        have h' := h.comp (tendsto_add_atTop_nat 1)
        refine h'.congr fun T => ?_
        simp only [Function.comp_apply]; push_cast; ring
      refine this.congr fun T => ?_
      congr 1; ring
    simpa using h1.const_mul K
  have hlim' := (ENNReal.continuous_ofReal.tendsto K).comp hlim
  rw [← hlim'.limsup_eq]
  exact limsup_le_limsup (Eventually.of_forall hb)

end L5D


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5E
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw)

/-- The two lower supports agree. -/
lemma lowerSupport_eq : PerishBaseStock.Outdating.lowerSupport P = (lowerSupport P : ℝ) := by
  unfold PerishBaseStock.Outdating.lowerSupport lowerSupport PerishBaseStock.Outdating.cdf
  have hset : {x : ℝ | 0 < P.law {d : ℝ≥0 | (d : ℝ) ≤ x}} =
      (fun x : ℝ≥0 => (x : ℝ)) '' {x : ℝ≥0 | 0 < P.law (Set.Iic x)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hx
      have hx0 : 0 ≤ x := by
        by_contra hneg
        push Not at hneg
        have : {d : ℝ≥0 | (d : ℝ) ≤ x} = ∅ := by
          ext d; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          linarith [d.2]
        rw [this, measure_empty] at hx; exact lt_irrefl _ hx
      refine ⟨x.toNNReal, ?_, Real.coe_toNNReal _ hx0⟩
      have : Set.Iic x.toNNReal = {d : ℝ≥0 | (d : ℝ) ≤ x} := by
        ext d; simp only [Set.mem_Iic, Set.mem_ofPred_eq]
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0]
      rw [this]; exact hx
    · rintro ⟨y, hy, rfl⟩
      have : {d : ℝ≥0 | (d : ℝ) ≤ y} = Set.Iic y := by
        ext d; simp
      rw [this]; exact hy
  rw [hset, NNReal.coe_sInf]

/-- The Outdating parameters with the same `m, h, p`. -/
def cO (c : Params) (hc : c.Standing) : PerishBaseStock.Outdating.Params :=
  ⟨c.m, hc.one_le_m, c.h, c.p, hc.h_pos, hc.p_pos⟩

lemma heurCost_eq (c : Params) (hc : c.Standing) (θ : ℝ≥0) (S : ℝ≥0) :
    PerishBaseStock.Outdating.heurCost P (cO c hc) θ S = tildeC P { c with θ := (θ : ℝ) } S := rfl

lemma isHeurMin_iff (c : Params) (hc : c.Standing) (θ : ℝ≥0) (S : ℝ≥0) :
    PerishBaseStock.Outdating.IsHeurMin P (cO c hc) θ S ↔
      IsTildeMinimizer P { c with θ := (θ : ℝ) } S := Iff.rfl

lemma least_isMin (c : Params) (hc : c.Standing) (θ : ℝ≥0) :
    PerishBaseStock.Outdating.IsHeurMin P (cO c hc) θ
      (PerishBaseStock.Outdating.leastHeurMin P (cO c hc) θ) := by
  have hcθ : ({ c with θ := (θ : ℝ) } : Params).Standing :=
    ⟨hc.one_le_m, hc.h_pos, hc.p_pos, θ.2⟩
  obtain ⟨S, -, hS⟩ := L5H.tilde_exists P _ hcθ
  have hclosed : IsClosed {S : ℝ≥0 | PerishBaseStock.Outdating.IsHeurMin P (cO c hc) θ S} := by
    have : {S : ℝ≥0 | PerishBaseStock.Outdating.IsHeurMin P (cO c hc) θ S} =
        ⋂ S' : ℝ≥0, {S | tildeC P { c with θ := (θ : ℝ) } S ≤
          tildeC P { c with θ := (θ : ℝ) } S'} := by
      ext S; simp [PerishBaseStock.Outdating.IsHeurMin, heurCost_eq]
    rw [this]
    exact isClosed_iInter fun S' => isClosed_le (L5H.tildeC_cont P _) continuous_const
  exact hclosed.csInf_mem ⟨S, (isHeurMin_iff P c hc θ S).2 hS⟩ (OrderBot.bddBelow _)

lemma tendsto_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by
    rw [← Real.toNNReal_coe (r := b)]; exact Real.toNNReal_le_toNNReal ha⟩

/-- OPT is monotone in `θ ≥ 0`. -/
lemma OPT_mono (c : Params) (hc : c.Standing) {θ θ' : ℝ} (h0 : 0 ≤ θ) (h : θ ≤ θ') :
    OPT P { c with θ := θ } ≤ OPT P { c with θ := θ' } := by
  refine iInf_mono fun π => ?_
  unfold policyCost
  refine limsup_le_limsup (Eventually.of_forall fun T => ?_)
  refine ENNReal.div_le_div_right (Finset.sum_le_sum fun t _ => lintegral_mono fun d => ?_) _
  unfold periodCost
  refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have := (L5D.inv_run π hc.one_le_m d t).outdate_nonneg
    (NNReal.coe_nonneg (π.φ t (run π d t))) (d t : ℝ)
  exact mul_le_mul_of_nonneg_right h this

end L5E

namespace L5E
open PerishBaseStock.Lifo

theorem ec21 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (St : ℝ → ℝ≥0) (hSt : ∀ θ : ℝ, 0 ≤ θ → IsTildeMinimizer P { c with θ := θ } (St θ)) :
    Tendsto (fun θ : ℝ => tildeC P { c with θ := θ } (St θ)) atTop
        (𝓝 (⨅ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
          backorderCost P.law c.h c.p S.val)) ∧
      ∃ L : ℝ≥0∞, Tendsto (fun θ : ℝ => OPT P { c with θ := θ }) atTop (𝓝 L) ∧
        ENNReal.ofReal (⨅ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
          backorderCost P.law c.h c.p S.val) ≤ L := by
  set c' := cO c hc
  have hLS := lowerSupport_eq P
  set I := ⨅ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
    backorderCost P.law c.h c.p S.val with hI
  have hne : Nonempty {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)} :=
    ⟨⟨0, by simp only [NNReal.coe_zero]; positivity⟩⟩
  set least := PerishBaseStock.Outdating.leastHeurMin P c'
  have hleast : ∀ θ' : ℝ≥0, PerishBaseStock.Outdating.IsHeurMin P c' θ' (least θ') :=
    least_isMin P c hc
  obtain ⟨Sinf, -, hlimN, hnvmin⟩ := PerishBaseStock.Outdating.eq_EC17 P c'
  have h24 := PerishBaseStock.Outdating.eq_24 P c' least hleast
  have hm0 : (0 : ℝ) < c.m := by exact_mod_cast hc.one_le_m
  -- the least-minimizer values converge
  have hW : Tendsto (fun θ' : ℝ≥0 => PerishBaseStock.Outdating.heurCost P c' θ' (least θ')) atTop
      (𝓝 (PerishBaseStock.Outdating.nvCost P c' Sinf)) := by
    have : (fun θ' : ℝ≥0 => PerishBaseStock.Outdating.heurCost P c' θ' (least θ')) = fun θ' =>
        PerishBaseStock.Outdating.nvCost P c' (least θ') + (1 / (c.m : ℝ)) *
          ((θ' : ℝ) * PerishBaseStock.Outdating.excessOverLifetimeDemand P c' (least θ')) := by
      funext θ'; unfold PerishBaseStock.Outdating.heurCost; simp only [c', cO]; ring
    rw [this]
    simpa using hlimN.add (h24.const_mul (1 / (c.m : ℝ)))
  -- every minimizer has the same value
  have hV : ∀ θ : ℝ, 0 ≤ θ → tildeC P { c with θ := θ } (St θ) =
      PerishBaseStock.Outdating.heurCost P c' θ.toNNReal (least θ.toNNReal) := by
    intro θ hθ
    have hθ' : ((θ.toNNReal : ℝ≥0) : ℝ) = θ := Real.coe_toNNReal _ hθ
    have h1 := hleast θ.toNNReal (St θ)
    have h2 := hSt θ hθ (least θ.toNNReal)
    rw [heurCost_eq, heurCost_eq, hθ'] at h1
    rw [heurCost_eq, hθ']
    exact le_antisymm h2 h1
  have hVlim : Tendsto (fun θ : ℝ => tildeC P { c with θ := θ } (St θ)) atTop
      (𝓝 (PerishBaseStock.Outdating.nvCost P c' Sinf)) := by
    refine (hW.comp tendsto_toNNReal_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with θ hθ
    exact (hV θ hθ).symm
  -- upper bound by every admissible newsvendor level
  have hupper : ∀ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
      PerishBaseStock.Outdating.nvCost P c' Sinf ≤ backorderCost P.law c.h c.p S.val := by
    intro S
    refine le_of_tendsto hVlim ?_
    filter_upwards [eventually_ge_atTop 0] with θ hθ
    have hθ' : ((θ.toNNReal : ℝ≥0) : ℝ) = θ := Real.coe_toNNReal _ hθ
    have hmin : PerishBaseStock.Outdating.IsHeurMin P c' θ.toNNReal (St θ) := by
      rw [isHeurMin_iff, hθ']; exact hSt θ hθ
    have := (PerishBaseStock.Outdating.eq_EC16 P c' θ.toNNReal (St θ) hmin).2.2 S.val
      (by rw [hLS]; exact S.2)
    rw [heurCost_eq, hθ'] at this
    exact this
  have hbdd : BddBelow (Set.range fun S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)} =>
      backorderCost P.law c.h c.p S.val) :=
    ⟨0, by
      rintro _ ⟨S, rfl⟩
      exact add_nonneg (mul_nonneg hc.h_pos.le (L5H.EH_nonneg _ _))
        (mul_nonneg hc.p_pos.le (L5H.ES_nonneg _ _))⟩
  have hle1 : PerishBaseStock.Outdating.nvCost P c' Sinf ≤ I := le_ciInf hupper
  have hle2 : I ≤ PerishBaseStock.Outdating.nvCost P c' Sinf := by
    refine le_trans ?_ hnvmin
    unfold PerishBaseStock.Outdating.nvMinBelow
    rw [hLS, sInf_image']
    rfl
  have hEq : PerishBaseStock.Outdating.nvCost P c' Sinf = I := le_antisymm hle1 hle2
  rw [hEq] at hVlim
  refine ⟨hVlim, ?_⟩
  -- OPT converges by monotonicity
  set f : ℝ → ℝ≥0∞ := fun θ => OPT P { c with θ := max θ 0 }
  have hf : Monotone f := fun a b hab =>
    OPT_mono P c hc (le_max_right _ _) (max_le_max hab le_rfl)
  refine ⟨⨆ θ, f θ, ?_, ?_⟩
  · refine (tendsto_atTop_iSup hf).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with θ hθ
    simp only [f, max_eq_left hθ]
  · have hV' := (ENNReal.continuous_ofReal.tendsto I).comp hVlim
    refine le_of_tendsto hV' ?_
    filter_upwards [eventually_ge_atTop 0] with θ hθ
    have hcθ : ({ c with θ := θ } : Params).Standing := ⟨hc.one_le_m, hc.h_pos, hc.p_pos, hθ⟩
    have h1 := L5D.prop2 P _ hcθ (St θ) (hSt θ hθ)
    have h2 : OPT P { c with θ := θ } ≤ ⨆ θ, f θ := by
      have := le_iSup f θ
      simp only [f, max_eq_left hθ] at this
      exact this
    exact h1.trans h2

end L5E


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic
open PerishBaseStock.Lifo

theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (St : ℝ → ℝ≥0) (hSt : ∀ θ : ℝ, 0 ≤ θ → IsTildeMinimizer P { c with θ := θ } (St θ)) :
    Tendsto (fun θ : ℝ => tildeC P { c with θ := θ } (St θ)) atTop
        (𝓝 (⨅ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
          backorderCost P.law c.h c.p S.val)) ∧
      ∃ L : ℝ≥0∞, Tendsto (fun θ : ℝ => OPT P { c with θ := θ }) atTop (𝓝 L) ∧
        ENNReal.ofReal (⨅ S : {S : ℝ≥0 // (S : ℝ) ≤ c.m * (lowerSupport P : ℝ)},
          backorderCost P.law c.h c.p S.val) ≤ L :=
  L5E.ec21 P c hc St hSt
