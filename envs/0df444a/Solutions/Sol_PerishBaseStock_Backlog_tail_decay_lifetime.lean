-- Prove2me | solution 1 for PerishBaseStock.Backlog.tail_decay_lifetime
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:38:16.241904+00:00
-- url     : https://prove2.me/submissions/e15df4c7-027a-44e5-b9d7-e9f6eddaa061

import Definitions.Def_PerishBaseStock_Backlog_Model
import Mathlib.Probability.Moments.Basic

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

namespace PB7H
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock

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

end PB7H

namespace PB7L
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H ProbabilityTheory

theorem indep (P : DemandLaw) :
    iIndepFun (fun i (d : DemandPath) => ((d i : ℝ≥0) : ℝ)) (demandPathLaw P) := by
  unfold demandPathLaw
  exact iIndepFun_infinitePi (X := fun _ (x : ℝ≥0) => (x : ℝ)) (fun _ => by fun_prop)

theorem mgf_coord (P : DemandLaw) (i : ℕ) :
    mgf (fun d : DemandPath => ((d i : ℝ≥0) : ℝ)) (demandPathLaw P) (-1) =
      ∫ x : ℝ≥0, Real.exp (-(x : ℝ)) ∂P.law := by
  have h : (demandPathLaw P).map (fun d => d i) = P.law := Measure.infinitePi_map_eval _ i
  unfold mgf
  rw [← h, integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
  simp

theorem q_lt_one (P : DemandLaw) : ∫ x : ℝ≥0, Real.exp (-(x : ℝ)) ∂P.law < 1 := by
  by_contra hcon
  push Not at hcon
  have hint : Integrable (fun x : ℝ≥0 => Real.exp (-(x : ℝ))) P.law := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by simp)
  have hnn : 0 ≤ᵐ[P.law] fun x : ℝ≥0 => 1 - Real.exp (-(x : ℝ)) :=
    ae_of_all _ fun x => by
      have : Real.exp (-(x : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
      simp only [Pi.zero_apply]; linarith
  have hzero : ∫ x : ℝ≥0, (1 - Real.exp (-(x : ℝ))) ∂P.law = 0 := by
    rw [integral_sub (integrable_const _) hint]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have : 0 ≤ ∫ x : ℝ≥0, (1 - Real.exp (-(x : ℝ))) ∂P.law := integral_nonneg_of_ae hnn
    rw [integral_sub (integrable_const _) hint] at this
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    linarith
  rw [integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const _).sub hint)] at hzero
  have hx0 : (fun x : ℝ≥0 => (x : ℝ)) =ᵐ[P.law] 0 := by
    filter_upwards [hzero] with x hx
    simp only [Pi.zero_apply, sub_eq_zero] at hx ⊢
    have := Real.exp_eq_one_iff (-(x : ℝ)) |>.1 hx.symm
    linarith
  have := P.positiveMean
  rw [integral_congr_ae hx0] at this
  simp at this

theorem q_pos (P : DemandLaw) : 0 < ∫ x : ℝ≥0, Real.exp (-(x : ℝ)) ∂P.law := by
  have hint : Integrable (fun x : ℝ≥0 => Real.exp (-(x : ℝ))) P.law := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by simp)
  exact integral_exp_pos hint

/-- Chernoff-type bound: `E[(S - Σ_{i<k} D_i)^+] ≤ S e^S q^k`. -/
theorem tail_bound (P : DemandLaw) (k : ℕ) (S : ℝ≥0) :
    expectedHolding (leadTimeLaw P k) S ≤
      (S : ℝ) * Real.exp S * (∫ x : ℝ≥0, Real.exp (-(x : ℝ)) ∂P.law) ^ (k + 1) := by
  unfold expectedHolding leadTimeLaw
  rw [integral_map (meas_sum k).aemeasurable (by fun_prop)]
  set X : ℕ → DemandPath → ℝ := fun i d => ((d i : ℝ≥0) : ℝ)
  have hm := (indep P).mgf_sum (fun i => by fun_prop) (Finset.range (k + 1)) (t := -1)
  simp only [mgf_coord, Finset.prod_const, Finset.card_range] at hm
  rw [← hm]
  unfold mgf
  rw [← integral_const_mul]
  have hint : Integrable (fun d : DemandPath =>
      Real.exp (-1 * (∑ i ∈ Finset.range (k + 1), X i) d)) (demandPathLaw P) := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_one_iff.2 ?_
    simp only [Finset.sum_apply, X]
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ) :=
      Finset.sum_nonneg fun i _ => (d i).2
    linarith
  have hint2 : Integrable (fun d : DemandPath =>
      max ((S : ℝ) - ((∑ i ∈ Finset.range (k + 1), d i : ℝ≥0) : ℝ)) 0) (demandPathLaw P) := by
    refine Integrable.of_bound (by fun_prop) (S : ℝ) (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [(∑ i ∈ Finset.range (k + 1), d i).2]) S.2
  refine integral_mono hint2 (hint.const_mul _) fun d => ?_
  · simp only [Finset.sum_apply, X, NNReal.coe_sum]
    set y := ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ)
    have hy : 0 ≤ y := Finset.sum_nonneg fun i _ => (d i).2
    have hS : (0 : ℝ) ≤ S := S.2
    rcases le_total ((S : ℝ) - y) 0 with h | h
    · rw [max_eq_right h]; positivity
    · rw [max_eq_left h]
      have e : Real.exp S * Real.exp (-1 * y) = Real.exp (S - y) := by
        rw [← Real.exp_add]; ring_nf
      rw [mul_assoc, e]
      have : 1 ≤ Real.exp ((S : ℝ) - y) := Real.one_le_exp h
      nlinarith

end PB7L

open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic PB7H PB7L in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ K₂ : ℝ, 0 < K₂ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ S : ℝ≥0, IsHeuristicLevel P { c with m := m } S →
        expectedHolding (leadTimeLaw P (m + c.L - 1)) S ≤ K₁ * Real.exp (-(K₂ * m)) := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  set μ1 := leadTimeLaw P c.L
  have hi1 := lead_integrable P c.L
  set M1 := ∫ x : ℝ≥0, (x : ℝ) ∂μ1
  have hM1 : 0 ≤ M1 := integral_nonneg fun x => x.2
  set B : ℝ := M1 + c.b * M1 / c.h
  have hB : 0 ≤ B := by positivity
  set q := ∫ x : ℝ≥0, Real.exp (-(x : ℝ)) ∂P.law
  have hq1 := q_lt_one P
  have hq0 := q_pos P
  refine ⟨B * Real.exp B + 1, by positivity, -Real.log q, by
    have := Real.log_neg hq0 hq1; linarith, fun m hm S hS => ?_⟩
  -- bound on the heuristic level
  have hSB : (S : ℝ) ≤ B := by
    have h := hS 0
    unfold heuristicCost at h
    simp only [eh_zero, mul_zero, zero_add, add_zero] at h
    have hES0 : expectedShortfall μ1 0 = M1 := by
      unfold expectedShortfall
      congr 1; ext x; simp [x.2]
    rw [hES0] at h
    have h1 := eh_ge μ1 hi1 S
    have h2 := es_nonneg μ1 S
    have hL0 : (0 : ℝ) ≤ c.L := Nat.cast_nonneg _
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h3 : 0 ≤ (c.θ - c.h * c.L) / ((m : ℝ) + c.L) *
        expectedHolding (leadTimeLaw P (m + c.L - 1)) S :=
      mul_nonneg (div_nonneg (by linarith) (by positivity)) (eh_nonneg _ _)
    have h4 : c.h * ((S : ℝ) - M1) ≤ c.b * M1 := by
      have := mul_le_mul_of_nonneg_left h1 hh.le
      have := mul_nonneg hb.le h2
      change c.h * expectedHolding μ1 S + c.b * expectedShortfall μ1 S +
        (c.θ - c.h * c.L) / ((m : ℝ) + c.L) *
          expectedHolding (leadTimeLaw P (m + c.L - 1)) S ≤ c.b * M1 at h
      linarith
    have : (S : ℝ) - M1 ≤ c.b * M1 / c.h := by
      rw [le_div_iff₀ hh]; linarith
    linarith
  have ht := tail_bound P (m + c.L - 1) S
  have hk : m + c.L - 1 + 1 = m + c.L := by omega
  rw [hk] at ht
  have hqm : q ^ (m + c.L) ≤ q ^ m := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
  have hqexp : q ^ m = Real.exp (-(-Real.log q * m)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq0]; congr 1; ring
  have hS0 : (0 : ℝ) ≤ S := S.2
  calc expectedHolding (leadTimeLaw P (m + c.L - 1)) S
      ≤ (S : ℝ) * Real.exp S * q ^ (m + c.L) := ht
    _ ≤ B * Real.exp B * q ^ m := by
        apply mul_le_mul _ hqm (by positivity) (by positivity)
        exact mul_le_mul hSB (Real.exp_le_exp.2 hSB) (by positivity) hB
    _ ≤ (B * Real.exp B + 1) * q ^ m := by
        have : 0 ≤ q ^ m := by positivity
        nlinarith
    _ = _ := by rw [hqexp]
