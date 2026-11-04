-- Prove2me | solution 1 for PerishBaseStock.Lifetime.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T00:39:49.161872+00:00
-- url     : https://prove2.me/submissions/6ffb61b4-084f-45af-8a72-d53d286d9762

import Theorems.Thm_PerishBaseStock_Lifetime_eq_21_gap_bound
import Mathlib.Probability.Moments.Basic

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace PerishLifetimeThm1Aux
open LostSalesOrderUpTo.Asymptotic CappedBaseStock

lemma meas_sum (k : ℕ) :
    Measurable (fun d : DemandPath => ∑ i ∈ Finset.range (k + 1), d i) := by fun_prop

lemma eh_int (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (S : ℝ≥0) :
    Integrable (fun x : ℝ≥0 => max ((S : ℝ) - x) 0) μ := by
  refine Integrable.of_bound (by fun_prop) (S : ℝ) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [x.2]) S.2

lemma es_int (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (S : ℝ≥0) :
    Integrable (fun x : ℝ≥0 => max ((x : ℝ) - S) 0) μ := by
  refine hμ.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [S.2]) x.2

lemma eh_mono (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {S S' : ℝ≥0} (h : S ≤ S') :
    expectedHolding μ S ≤ expectedHolding μ S' :=
  integral_mono (eh_int μ S) (eh_int μ S') fun x =>
    max_le_max (by have : (S : ℝ) ≤ S' := h; linarith) le_rfl

lemma eh_nonneg (μ : Measure ℝ≥0) (S : ℝ≥0) : 0 ≤ expectedHolding μ S :=
  integral_nonneg fun _ => le_max_right _ _

lemma indep (P : DemandLaw) :
    iIndepFun (fun i (d : DemandPath) => ((d i : ℝ≥0) : ℝ)) (demandPathLaw P) := by
  unfold demandPathLaw
  exact iIndepFun_infinitePi (X := fun _ (x : ℝ≥0) => (x : ℝ)) (fun _ => by fun_prop)

lemma mgf_coord (P : DemandLaw) (i : ℕ) (lam : ℝ) :
    mgf (fun d : DemandPath => ((d i : ℝ≥0) : ℝ)) (demandPathLaw P) (-lam) =
      ∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂P.law := by
  have h : (demandPathLaw P).map (fun d => d i) = P.law := Measure.infinitePi_map_eval _ i
  unfold mgf
  rw [← h, integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
  simp [neg_mul]

/-- Pointwise: `y^+ ≤ e^{λ y - 1} / λ`. -/
lemma pos_le_exp {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    max y 0 ≤ Real.exp (lam * y - 1) / lam := by
  have h1 := Real.add_one_le_exp (lam * y - 1)
  have h2 : 0 < Real.exp (lam * y - 1) := Real.exp_pos _
  apply max_le
  · rw [le_div_iff₀ hlam]; linarith
  · positivity

/-- Chernoff bound: `E[(S - Σ_{i ≤ k} D_i)^+] ≤ e^{λS}/(λe) · (E e^{-λD})^{k+1}`. -/
lemma tail_bound (P : DemandLaw) {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (S : ℝ≥0) :
    expectedHolding (leadTimeLaw P k) S ≤
      Real.exp (lam * S) / (lam * Real.exp 1) *
        (∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂P.law) ^ (k + 1) := by
  unfold expectedHolding leadTimeLaw
  rw [integral_map (meas_sum k).aemeasurable (by fun_prop)]
  set X : ℕ → DemandPath → ℝ := fun i d => ((d i : ℝ≥0) : ℝ)
  have hm := (indep P).mgf_sum (fun i => by fun_prop) (Finset.range (k + 1)) (t := -lam)
  simp only [mgf_coord, Finset.prod_const, Finset.card_range] at hm
  rw [← hm]
  unfold mgf
  rw [← integral_const_mul]
  have hint : Integrable (fun d : DemandPath =>
      Real.exp (-lam * (∑ i ∈ Finset.range (k + 1), X i) d)) (demandPathLaw P) := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_one_iff.2 ?_
    simp only [Finset.sum_apply, X]
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ) :=
      Finset.sum_nonneg fun i _ => (d i).2
    nlinarith
  have hint2 : Integrable (fun d : DemandPath =>
      max ((S : ℝ) - ((∑ i ∈ Finset.range (k + 1), d i : ℝ≥0) : ℝ)) 0) (demandPathLaw P) := by
    refine Integrable.of_bound (by fun_prop) (S : ℝ) (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [(∑ i ∈ Finset.range (k + 1), d i).2]) S.2
  refine integral_mono hint2 (hint.const_mul _) fun d => ?_
  simp only [Finset.sum_apply, NNReal.coe_sum]
  set y := ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ)
  have e : Real.exp (lam * S) / (lam * Real.exp 1) * Real.exp (-lam * y) =
      Real.exp (lam * ((S : ℝ) - y) - 1) / lam := by
    rw [show lam * ((S : ℝ) - y) - 1 = lam * S + -lam * y - 1 by ring, Real.exp_sub,
      Real.exp_add]
    field_simp
  rw [e]
  exact pos_le_exp hlam _

/-- The critical-fractile level is attained: `F(S^NP) ≥ p/(p+h)`. -/
lemma newsvendor_mem (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] {h p : ℝ} (hh : 0 < h)
    (hp : 0 < p) :
    ENNReal.ofReal (p / (p + h)) ≤ μ (Set.Iic (newsvendorLevel μ h p)) := by
  set a := ENNReal.ofReal (p / (p + h)) with ha
  set A : Set ℝ≥0 := {S : ℝ≥0 | a ≤ distribution μ S} with hA
  have ha1 : a < 1 := by
    rw [ha, ENNReal.ofReal_lt_one, div_lt_one (by linarith)]; linarith
  -- nonempty
  have hne : A.Nonempty := by
    have hmono : Monotone (fun n : ℕ => Set.Iic (n : ℝ≥0)) := fun i j hij =>
      Set.Iic_subset_Iic.2 (by exact_mod_cast hij)
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    have hU : (⋃ n : ℕ, Set.Iic (n : ℝ≥0)) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hn⟩
    rw [hU, measure_univ] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds ha1)).exists
    exact ⟨n, le_of_lt hn⟩
  set s0 := sInf A with hs0
  have hmemn : ∀ n : ℕ, s0 + 1 / ((n : ℝ≥0) + 1) ∈ A := by
    intro n
    have hlt : s0 < s0 + 1 / ((n : ℝ≥0) + 1) := by
      apply lt_add_of_pos_right; positivity
    obtain ⟨b, hb, hb'⟩ := exists_lt_of_csInf_lt hne hlt
    show a ≤ μ (Set.Iic _)
    exact le_trans hb (measure_mono (Set.Iic_subset_Iic.2 hb'.le))
  have hanti : Antitone (fun n : ℕ => Set.Iic (s0 + 1 / ((n : ℝ≥0) + 1))) := by
    intro i j hij
    apply Set.Iic_subset_Iic.2
    have : 1 / ((j : ℝ≥0) + 1) ≤ 1 / ((i : ℝ≥0) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (i : ℝ≥0) ≤ j := by exact_mod_cast hij
      exact add_le_add_left this 1
    gcongr
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hI : (⋂ n : ℕ, Set.Iic (s0 + 1 / ((n : ℝ≥0) + 1))) = Set.Iic s0 := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Iic]
    constructor
    · intro hx
      by_contra hcon
      push Not at hcon
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hcon)
      have := hx n
      have h2 : s0 + 1 / ((n : ℝ≥0) + 1) < x := lt_tsub_iff_left.1 hn
      exact absurd this (not_le.2 h2)
    · intro hx n
      exact le_trans hx le_self_add
  rw [hI] at ht
  exact ge_of_tendsto' ht (fun n => hmemn n)

/-- `N(S) = hE[(S-D)^+] + pE[(D-S)^+]` is nondecreasing to the right of any `S₀`
with `F(S₀) ≥ p/(p+h)`. -/
lemma backorder_mono (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) {h p : ℝ} (hh : 0 < h) (hp : 0 < p)
    {S0 S : ℝ≥0} (hSS : S0 ≤ S) (hF : p / (p + h) ≤ (μ (Set.Iic S0)).toReal) :
    backorderCost μ h p S0 ≤ backorderCost μ h p S := by
  have hN : ∀ S : ℝ≥0, backorderCost μ h p S =
      ∫ x : ℝ≥0, (h * max ((S : ℝ) - x) 0 + p * max ((x : ℝ) - S) 0) ∂μ := by
    intro S
    unfold backorderCost expectedHolding expectedShortfall
    rw [integral_add ((eh_int μ S).const_mul h) ((es_int μ hμ S).const_mul p),
      integral_const_mul, integral_const_mul]
  set φ : ℝ≥0 → ℝ := fun x =>
    ((S : ℝ) - S0) * ((h + p) * (Set.Iic S0).indicator (fun _ => (1 : ℝ)) x - p) with hφ
  have hφint : Integrable φ μ :=
    (((integrable_const (1 : ℝ)).indicator measurableSet_Iic).const_mul (h + p)
      |>.sub (integrable_const p)).const_mul _
  have hφval : ∫ x, φ x ∂μ = ((S : ℝ) - S0) * ((h + p) * (μ (Set.Iic S0)).toReal - p) := by
    simp only [hφ]
    rw [integral_const_mul, integral_sub (((integrable_const (1 : ℝ)).indicator
      measurableSet_Iic).const_mul (h + p)) (integrable_const p), integral_const_mul,
      integral_indicator_const _ measurableSet_Iic]
    simp [measureReal_def]
  have hSS' : (S0 : ℝ) ≤ S := hSS
  have hφnn : 0 ≤ ∫ x, φ x ∂μ := by
    rw [hφval]
    apply mul_nonneg (by linarith)
    rw [div_le_iff₀ (by linarith)] at hF
    linarith
  have i0 : Integrable (fun x : ℝ≥0 => h * max ((S0 : ℝ) - x) 0 + p * max ((x : ℝ) - S0) 0) μ :=
    ((eh_int μ S0).const_mul h).add ((es_int μ hμ S0).const_mul p)
  have i1 : Integrable (fun x : ℝ≥0 => h * max ((S : ℝ) - x) 0 + p * max ((x : ℝ) - S) 0) μ :=
    ((eh_int μ S).const_mul h).add ((es_int μ hμ S).const_mul p)
  have key : ∫ x : ℝ≥0, ((h * max ((S0 : ℝ) - x) 0 + p * max ((x : ℝ) - S0) 0) + φ x) ∂μ ≤
      ∫ x : ℝ≥0, (h * max ((S : ℝ) - x) 0 + p * max ((x : ℝ) - S) 0) ∂μ := by
    refine integral_mono (i0.add hφint) i1 (fun x => ?_)
    simp only [hφ]
    by_cases hx : x ∈ Set.Iic S0
    · rw [Set.indicator_of_mem hx]
      have hx' : (x : ℝ) ≤ S0 := hx
      rw [max_eq_left (by linarith : (0:ℝ) ≤ (S0 : ℝ) - x), max_eq_right (by linarith : (x:ℝ) - S0 ≤ 0),
        max_eq_left (by linarith : (0:ℝ) ≤ (S : ℝ) - x), max_eq_right (by linarith : (x:ℝ) - S ≤ 0)]
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      have hx' : (S0 : ℝ) < x := not_le.1 hx
      rw [max_eq_right (by linarith : (S0 : ℝ) - x ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ (x:ℝ) - S0)]
      rcases le_total (x : ℝ) S with hxs | hxs
      · rw [max_eq_left (by linarith : (0:ℝ) ≤ (S : ℝ) - x), max_eq_right (by linarith : (x:ℝ) - S ≤ 0)]
        nlinarith
      · rw [max_eq_right (by linarith : (S : ℝ) - x ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ (x:ℝ) - S)]
        nlinarith
  rw [integral_add i0 hφint] at key
  rw [hN S0, hN S]
  linarith

end PerishLifetimeThm1Aux

open PerishBaseStock.Lifetime PerishLifetimeThm1Aux LostSalesOrderUpTo.Asymptotic in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (lam : ℝ) (hlam : 0 < lam)
    (Stilde : ℝ≥0) (hS : IsHeuristicLevel P c Stilde) :
    bsCost P c Stilde ≤ OPT P c + ENNReal.ofReal (((c.m : ℝ) - 1) * c.θ / (lam * c.m * Real.exp 1) *
      Real.exp (lam * (newsvendorNP P c : ℝ)) *
      (∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂P.law) ^ c.m) := by
  have hm := c.one_le_m
  have hmR : (0 : ℝ) < c.m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) ≤ (c.m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ c.m := by exact_mod_cast hm
    linarith
  have hθ := c.θ_nonneg
  have : IsProbabilityMeasure (leadTimeLaw P (c.m - 1)) := by
    unfold leadTimeLaw
    exact Measure.isProbabilityMeasure_map (meas_sum _).aemeasurable
  set S1 := newsvendorNP P c with hS1
  set g : ℝ≥0 → ℝ := fun S => expectedHolding (leadTimeLaw P (c.m - 1)) S with hg
  set q := ∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂P.law with hq
  -- Step 1: θ g(S̃) ≤ θ g(S^NP) for every minimizer S̃.
  have hstep : c.θ * g Stilde ≤ c.θ * g S1 := by
    rcases le_total Stilde S1 with hle | hle
    · exact mul_le_mul_of_nonneg_left (eh_mono _ hle) hθ
    · have hF : c.p / (c.p + c.h) ≤ (P.law (Set.Iic S1)).toReal := by
        have h1 := newsvendor_mem P.law c.h_pos c.p_pos
        have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
        rwa [ENNReal.toReal_ofReal (div_nonneg c.p_pos.le (by linarith [c.p_pos, c.h_pos]))] at h2
      have hN := backorder_mono P.law P.finiteMean c.h_pos c.p_pos hle hF
      have hmin := hS S1
      unfold heuristicCost at hmin
      have h3 : c.θ / c.m * g Stilde ≤ c.θ / c.m * g S1 := by
        simp only [hg]; linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hmR.le
      have e1 : (c.m : ℝ) * (c.θ / c.m * g Stilde) = c.θ * g Stilde := by field_simp
      have e2 : (c.m : ℝ) * (c.θ / c.m * g S1) = c.θ * g S1 := by field_simp
      linarith
  -- Step 2: Chernoff bound at S^NP.
  have htail := tail_bound P hlam (c.m - 1) S1
  rw [show c.m - 1 + 1 = c.m by omega] at htail
  have hgap := eq_21_gap_bound P c Stilde hS
  refine le_trans hgap (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hcoef : 0 ≤ ((c.m : ℝ) - 1) / c.m := div_nonneg hm1 hmR.le
  calc ((c.m : ℝ) - 1) * c.θ / c.m * expectedHolding (leadTimeLaw P (c.m - 1)) Stilde
      = ((c.m : ℝ) - 1) / c.m * (c.θ * g Stilde) := by simp only [hg]; ring
    _ ≤ ((c.m : ℝ) - 1) / c.m * (c.θ * g S1) := mul_le_mul_of_nonneg_left hstep hcoef
    _ ≤ ((c.m : ℝ) - 1) / c.m * (c.θ * (Real.exp (lam * S1) / (lam * Real.exp 1) * q ^ c.m)) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        exact mul_le_mul_of_nonneg_left htail hθ
    _ = ((c.m : ℝ) - 1) * c.θ / (lam * c.m * Real.exp 1) * Real.exp (lam * S1) * q ^ c.m := by
        field_simp
