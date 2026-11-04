-- Prove2me | solution 1 for PerishBaseStock.Lifo.hat_S_theta_limits
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:10:24.194412+00:00
-- url     : https://prove2.me/submissions/18e4cc36-6d3e-4094-8ec5-dc41984197ca

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

namespace L5H
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw)

/-- `D ≥ D̲` almost surely. -/
lemma law_Iio_lowerSupport : P.law (Set.Iio (lowerSupport P)) = 0 := by
  set L := lowerSupport P with hLdef
  have hnull : ∀ x : ℝ≥0, x < L → P.law (Set.Iic x) = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ {x : ℝ≥0 | 0 < P.law (Set.Iic x)} := pos_iff_ne_zero.2 hne
    exact absurd (csInf_le (OrderBot.bddBelow _) hmem) (not_le.2 hx)
  rcases eq_or_ne L 0 with h0 | h0
  · rw [h0]; simp
  have hL : 0 < L := pos_iff_ne_zero.2 h0
  have hU : Set.Iio L = ⋃ n : ℕ, Set.Iic (L - 1 / ((n : ℝ≥0) + 1)) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      have hpos : (0 : ℝ) < (L : ℝ) - x := by
        have : (x : ℝ) < L := by exact_mod_cast hx
        linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      refine ⟨n, ?_⟩
      have h1 : 1 / ((n : ℝ≥0) + 1) ≤ L := by
        rw [← NNReal.coe_le_coe]; push_cast; linarith [x.2]
      rw [← NNReal.coe_le_coe, NNReal.coe_sub h1]
      push_cast; linarith
    · rintro ⟨n, hn⟩
      exact lt_of_le_of_lt hn (tsub_lt_self hL (by positivity))
  rw [hU]
  exact measure_iUnion_null fun n => hnull _ (tsub_lt_self hL (by positivity))

lemma EH_lowerSupport : expectedHolding P.law (lowerSupport P) = 0 := by
  unfold expectedHolding
  have hae : ∀ᵐ x ∂P.law, lowerSupport P ≤ x := by
    rw [ae_iff]
    have : {a : ℝ≥0 | ¬ lowerSupport P ≤ a} = Set.Iio (lowerSupport P) := by
      ext a; simp
    rw [this]; exact law_Iio_lowerSupport P
  rw [integral_eq_zero_of_ae]
  filter_upwards [hae] with x hx
  have : ((lowerSupport P : ℝ≥0) : ℝ) ≤ x := by exact_mod_cast hx
  simp only [Pi.zero_apply]
  exact max_eq_right (by linarith)

lemma ES_lowerSupport : expectedShortfall P.law (lowerSupport P) =
    CappedBaseStock.mean P - lowerSupport P := by
  rw [ES_eq_gen P.law P.finiteMean, EH_lowerSupport]
  unfold CappedBaseStock.mean; ring

end L5H


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5H
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable (P : CappedBaseStock.DemandLaw)

lemma exists_cdf_pos : ∃ x : ℝ≥0, 0 < P.law (Set.Iic x) := by
  by_contra h
  push Not at h
  have : P.law (⋃ n : ℕ, Set.Iic (n : ℝ≥0)) = 0 :=
    measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (h n)
  have hU : (⋃ n : ℕ, Set.Iic (n : ℝ≥0)) = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge x; exact ⟨n, hn⟩
  rw [hU, measure_univ] at this
  exact one_ne_zero this

lemma cdf_pos_above {x : ℝ≥0} (hx : lowerSupport P < x) : 0 < P.law (Set.Iic x) := by
  obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt (s := {x : ℝ≥0 | 0 < P.law (Set.Iic x)})
    (exists_cdf_pos P) hx
  exact lt_of_lt_of_le hy (measure_mono (Set.Iic_subset_Iic.mpr hyx.le))

lemma EH_pos_above {S : ℝ≥0} (hS : lowerSupport P < S) : 0 < expectedHolding P.law S := by
  set L := lowerSupport P
  set M : ℝ≥0 := (L + S) / 2
  have hLM : L < M := by
    rw [← NNReal.coe_lt_coe]; simp only [M, NNReal.coe_div, NNReal.coe_add]
    have : (L : ℝ) < S := by exact_mod_cast hS
    norm_num; linarith
  have hMS : M < S := by
    rw [← NNReal.coe_lt_coe]; simp only [M, NNReal.coe_div, NNReal.coe_add]
    have : (L : ℝ) < S := by exact_mod_cast hS
    norm_num; linarith
  have h1 := EH_sub_ge P.law hMS.le
  have h2 := EH_nonneg P.law M
  have hF : 0 < (P.law (Set.Iic M)).toReal :=
    ENNReal.toReal_pos (cdf_pos_above P hLM).ne' (measure_ne_top _ _)
  have hd : (0 : ℝ) < (S : ℝ) - M := by
    have : (M : ℝ) < S := by exact_mod_cast hMS
    linarith
  nlinarith [mul_pos hd hF]

lemma EH_le_low {S : ℝ≥0} (hS : S ≤ lowerSupport P) : expectedHolding P.law S = 0 :=
  le_antisymm ((EH_mono P.law hS).trans (EH_lowerSupport P).le) (EH_nonneg _ _)

lemma N_low {S : ℝ≥0} (hS : S ≤ lowerSupport P) (h p : ℝ) :
    backorderCost P.law h p S = backorderCost P.law h p (lowerSupport P) +
      p * ((lowerSupport P : ℝ) - S) := by
  unfold backorderCost
  rw [ES_eq_gen P.law P.finiteMean, ES_eq_gen P.law P.finiteMean, EH_le_low P hS,
    EH_lowerSupport]
  ring

lemma EHmax_lowerSupport (k : ℕ) : expectedHolding (maxLaw P k) (lowerSupport P) = 0 :=
  le_antisymm ((EH_max_le P k _).trans (EH_lowerSupport P).le) (EH_nonneg _ _)

lemma N_cont (h p : ℝ) : Continuous (fun S : ℝ≥0 => backorderCost P.law h p S) := by
  unfold backorderCost
  exact (continuous_const.mul (EH_cont P.law)).add (continuous_const.mul (ES_cont P))

end L5H

open PerishBaseStock.Lifo in
theorem L5H.hat_limits (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sh : ℝ → ℝ≥0) (hSh : ∀ θ : ℝ, 0 ≤ θ → IsHatMinimizer P { c with θ := θ } (Sh θ)) :
    Tendsto (fun θ : ℝ => (Sh θ : ℝ)) atTop (𝓝 (lowerSupport P : ℝ)) ∧
      Tendsto (fun θ : ℝ => θ * (expectedHolding P.law (Sh θ)
          + expectedHolding (maxLaw P (c.m - 1)) (Sh θ))) atTop (𝓝 0) := by
  set L := lowerSupport P with hL
  set N := fun S : ℝ≥0 => backorderCost P.law c.h c.p S with hNdef
  set G := fun S : ℝ≥0 => expectedHolding P.law S + expectedHolding (maxLaw P (c.m - 1)) S
    with hGdef
  have hm : (0 : ℝ) < c.m := by exact_mod_cast hc.one_le_m
  have hG0 : G L = 0 := by
    simp only [hGdef, hL, L5H.EH_lowerSupport, L5H.EHmax_lowerSupport]; ring
  have hGnn : ∀ S, 0 ≤ G S := fun S => add_nonneg (L5H.EH_nonneg _ _) (L5H.EH_nonneg _ _)
  have hNnn : ∀ S, 0 ≤ N S := fun S => add_nonneg
    (mul_nonneg hc.h_pos.le (L5H.EH_nonneg _ _)) (mul_nonneg hc.p_pos.le (L5H.ES_nonneg _ _))
  -- the key comparison with `S = D̲`
  have hcmp : ∀ θ : ℝ, 0 ≤ θ → N (Sh θ) + θ / c.m * G (Sh θ) / 2 ≤ N L := by
    intro θ hθ
    have := hSh θ hθ L
    rw [L5H.hatObjective_eq, L5H.hatObjective_eq] at this
    simp only at this
    have h0 : G L = 0 := hG0
    simp only [hGdef] at h0
    rw [h0] at this
    simpa using this
  have hge : ∀ θ : ℝ, 0 ≤ θ → L ≤ Sh θ := by
    intro θ hθ
    by_contra hlt
    push Not at hlt
    have h1 := hcmp θ hθ
    have h2 := L5H.N_low P hlt.le c.h c.p
    have h3 : 0 ≤ θ / c.m * G (Sh θ) / 2 := by
      have := hGnn (Sh θ); have : 0 ≤ θ / c.m := div_nonneg hθ hm.le; positivity
    have h4 : (0 : ℝ) < (L : ℝ) - Sh θ := by
      have : ((Sh θ : ℝ≥0) : ℝ) < L := by exact_mod_cast hlt
      linarith
    simp only [hNdef] at h1
    nlinarith [mul_pos hc.p_pos h4]
  have hGbd : ∀ θ : ℝ, 0 < θ → G (Sh θ) ≤ 2 * c.m * N L / θ := by
    intro θ hθ
    have h1 := hcmp θ hθ.le
    have h2 := hNnn (Sh θ)
    rw [le_div_iff₀ hθ]
    have : θ / c.m * G (Sh θ) = θ * G (Sh θ) / c.m := by ring
    rw [this] at h1
    have h3 : θ * G (Sh θ) / c.m / 2 ≤ N L := by linarith
    rw [div_div, div_le_iff₀ (by positivity)] at h3
    linarith
  have hGlim : Tendsto (fun θ : ℝ => 2 * c.m * N L / θ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  -- convergence of `Ŝ_θ`
  have hconv : Tendsto (fun θ : ℝ => (Sh θ : ℝ)) atTop (𝓝 (L : ℝ)) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [eventually_ge_atTop 0] with θ hθ
      have := hge θ hθ
      have : (L : ℝ) ≤ Sh θ := by exact_mod_cast this
      linarith
    · have hLa : L < a.toNNReal := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (le_trans L.2 ha.le)]; exact ha
      have hpos := L5H.EH_pos_above P hLa
      filter_upwards [eventually_gt_atTop 0,
        (hGlim.eventually (gt_mem_nhds hpos))] with θ hθ hθ2
      by_contra hcon
      push Not at hcon
      have hle : a.toNNReal ≤ Sh θ := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_trans L.2 ha.le)]; exact hcon
      have h1 := L5H.EH_mono P.law hle
      have h2 := hGbd θ hθ
      have h3 := L5H.EH_nonneg (maxLaw P (c.m - 1)) (Sh θ)
      simp only [hGdef] at h2
      linarith
  refine ⟨hconv, ?_⟩
  have hS : Tendsto Sh atTop (𝓝 L) := by rw [← NNReal.tendsto_coe]; exact hconv
  have hN : Tendsto (fun θ => N (Sh θ)) atTop (𝓝 (N L)) :=
    ((L5H.N_cont P c.h c.p).tendsto L).comp hS
  have hup : Tendsto (fun θ => 2 * c.m * (N L - N (Sh θ))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := N L)).sub hN
    simpa using this.const_mul (2 * (c.m : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with θ hθ
    exact mul_nonneg hθ (hGnn _)
  · filter_upwards [eventually_ge_atTop 0] with θ hθ
    have h1 := hcmp θ hθ
    have : θ / c.m * G (Sh θ) / 2 = θ * G (Sh θ) / (2 * c.m) := by field_simp
    rw [this, ← le_sub_iff_add_le', div_le_iff₀ (by positivity)] at h1
    simp only [hGdef] at h1 ⊢
    linarith


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic
open PerishBaseStock.Lifo

theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sh : ℝ → ℝ≥0) (hSh : ∀ θ : ℝ, 0 ≤ θ → IsHatMinimizer P { c with θ := θ } (Sh θ)) :
    Tendsto (fun θ : ℝ => (Sh θ : ℝ)) atTop (𝓝 (lowerSupport P : ℝ)) ∧
      Tendsto (fun θ : ℝ => θ * (expectedHolding P.law (Sh θ)
          + expectedHolding (maxLaw P (c.m - 1)) (Sh θ))) atTop (𝓝 0) :=
  L5H.hat_limits P c hc Sh hSh
