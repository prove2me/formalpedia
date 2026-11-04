-- Prove2me | solution 1 for PerishBaseStock.Lifo.ec_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:21:24.466688+00:00
-- url     : https://prove2.me/submissions/2b0958f4-9da0-4c2d-bd6f-128a704de16e

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

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
open PerishBaseStock.Lifo

theorem solution (P : CappedBaseStock.DemandLaw) (m : ℕ) (hm : 1 ≤ m) (S : ℝ≥0) (t : ℕ) :
    ENNReal.ofReal (expectedHolding (maxLaw P (m - 1)) S) ≤
      ∑ j ∈ Finset.Ico t (t + m),
        ∫⁻ d, ENNReal.ofReal (outdated (baseStock m S) d j) ∂CappedBaseStock.demandPathLaw P :=
  L5D.ec19 P hm S t
