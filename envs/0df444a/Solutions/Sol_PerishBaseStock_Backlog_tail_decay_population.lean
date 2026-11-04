-- Prove2me | solution 1 for PerishBaseStock.Backlog.tail_decay_population
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:22:21.906814+00:00
-- url     : https://prove2.me/submissions/b7de4315-7da4-4b35-9a45-3232f02a0dbe

import Definitions.Def_PerishBaseStock_Backlog_Model
import Definitions.Def_PerishBaseStock_Backlog_Population
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance

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
namespace PB7E
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H

theorem meas_sumR (k : ℕ) :
    Measurable (fun d : DemandPath => ∑ i ∈ Finset.range k, ((d i : ℝ≥0) : ℝ)) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).coe_nnreal_real

theorem eh_as (P : DemandLaw) (k : ℕ) (S : ℝ≥0) :
    expectedHolding (leadTimeLaw P k) S =
      ∫ d, max ((S : ℝ) - ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ)) 0 ∂demandPathLaw P := by
  unfold expectedHolding leadTimeLaw
  rw [integral_map (meas_sum k).aemeasurable (by fun_prop)]
  simp

theorem es_as (P : DemandLaw) (k : ℕ) (S : ℝ≥0) :
    expectedShortfall (leadTimeLaw P k) S =
      ∫ d, max (∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ) - S) 0 ∂demandPathLaw P := by
  unfold expectedShortfall leadTimeLaw
  rw [integral_map (meas_sum k).aemeasurable (by fun_prop)]
  simp

end PB7E

namespace PB7N
open ProbabilityTheory

/-! ## Generic i.i.d. toolkit on `ℕ → ℝ≥0` -/

section iid
variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

/-- Laplace transform / mgf of the one-dimensional law. -/
def lap (t : ℝ) : ℝ := ∫ x : ℝ≥0, Real.exp (t * x) ∂ρ

abbrev seq : Measure (ℕ → ℝ≥0) := Measure.infinitePi fun _ => ρ

def S (k : ℕ) (ω : ℕ → ℝ≥0) : ℝ := ∑ i ∈ Finset.range k, ((ω i : ℝ≥0) : ℝ)

theorem meas_S (k : ℕ) : Measurable (S k) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).coe_nnreal_real

theorem S_nonneg (k : ℕ) (ω : ℕ → ℝ≥0) : 0 ≤ S k ω :=
  Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _

theorem indep : iIndepFun (fun i (ω : ℕ → ℝ≥0) => ((ω i : ℝ≥0) : ℝ)) (seq ρ) :=
  iIndepFun_infinitePi (X := fun _ (x : ℝ≥0) => (x : ℝ)) (fun _ => by fun_prop)

theorem map_eval (i : ℕ) : (seq ρ).map (fun ω => ω i) = ρ := Measure.infinitePi_map_eval _ i

theorem integral_coord (f : ℝ≥0 → ℝ) (hf : Measurable f) (i : ℕ) :
    ∫ ω, f (ω i) ∂seq ρ = ∫ x, f x ∂ρ := by
  conv_rhs => rw [← map_eval ρ i]
  rw [integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]

theorem mgf_coord (i : ℕ) (t : ℝ) :
    mgf (fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) (seq ρ) t = lap ρ t := by
  unfold mgf lap
  exact integral_coord ρ (fun x => Real.exp (t * x)) (by fun_prop) i

theorem mgf_S (k : ℕ) (t : ℝ) : mgf (S k) (seq ρ) t = lap ρ t ^ k := by
  have hm := (indep ρ).mgf_sum (fun i => by fun_prop) (Finset.range k) (t := t)
  simp only [mgf_coord, Finset.prod_const, Finset.card_range] at hm
  rw [← hm]; congr 1; ext ω; simp [S]

theorem integrable_exp_neg (k : ℕ) {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun ω => Real.exp (-l * S k ω)) (seq ρ) := by
  refine Integrable.of_bound ((meas_S k).const_mul _).exp.aestronglyMeasurable 1
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [S_nonneg k ω])

/-- Chernoff lower-tail bound. -/
theorem lower_tail (k : ℕ) (ε : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    (seq ρ).real {ω | S k ω ≤ ε} ≤ Real.exp (l * ε) * lap ρ (-l) ^ k := by
  have := measure_le_le_exp_mul_mgf (μ := seq ρ) (X := S k) ε (t := -l) (by linarith)
    (integrable_exp_neg ρ k hl)
  rw [mgf_S] at this; simpa using this

theorem integrable_exp_coord {s : ℝ} (hs : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ρ)
    (i : ℕ) : Integrable (fun ω : ℕ → ℝ≥0 => Real.exp (s * ((ω i : ℝ≥0) : ℝ))) (seq ρ) := by
  have h : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ((seq ρ).map (fun ω => ω i)) := by
    rw [map_eval]; exact hs
  exact (integrable_map_measure h.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h

/-- Chernoff upper-tail bound. -/
theorem upper_tail (k : ℕ) (ε : ℝ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ρ) :
    (seq ρ).real {ω | ε ≤ S k ω} ≤ Real.exp (-s * ε) * lap ρ s ^ k := by
  have hint := (indep ρ).integrable_exp_mul_sum (t := s) (fun i => by fun_prop)
    (s := Finset.range k) (fun i _ => integrable_exp_coord ρ hs i)
  have hSeq : (∑ i ∈ Finset.range k, fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) = S k := by
    ext ω; simp [S]
  rw [hSeq] at hint
  have := measure_ge_le_exp_mul_mgf (μ := seq ρ) (X := S k) ε hs0 hint
  rwa [mgf_S] at this

end iid

/-! ## Elementary exponential inequalities -/

theorem exp_neg_le (y : ℝ) (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 := by
  have h1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
  have h2 : Real.exp (-y) * (1 + y) ≤ 1 := by
    have := Real.add_one_le_exp y
    calc Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y := by
          apply mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith

theorem exp_le (y : ℝ) (hy : 0 ≤ y) : Real.exp y ≤ 1 + y + y ^ 2 * Real.exp y := by
  -- e^y - 1 ≤ y e^y and e^y - 1 - y ≤ y (e^y - 1) ≤ y^2 e^y
  have h1 : Real.exp y - 1 ≤ y * Real.exp y := by
    have := Real.add_one_le_exp (-y)
    have h : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos y]
  nlinarith [Real.exp_pos y]

section bounds
variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

theorem lap_neg_le (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ)
    (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) {l : ℝ} (hl : 0 ≤ l) :
    lap ρ (-l) ≤ 1 - l * ∫ x : ℝ≥0, (x : ℝ) ∂ρ + l ^ 2 * ∫ x : ℝ≥0, (x : ℝ) ^ 2 ∂ρ := by
  unfold lap
  have hint : Integrable (fun x : ℝ≥0 => Real.exp (-l * x)) ρ := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [NNReal.coe_nonneg x])
  have hR : Integrable (fun x : ℝ≥0 => 1 - l * (x : ℝ) + l ^ 2 * (x : ℝ) ^ 2) ρ :=
    ((integrable_const _).sub (h1.const_mul _)).add (h2.const_mul _)
  calc ∫ x : ℝ≥0, Real.exp (-l * x) ∂ρ ≤ ∫ x : ℝ≥0, (1 - l * (x : ℝ) + l ^ 2 * (x : ℝ) ^ 2) ∂ρ :=
        integral_mono hint hR fun x => by
          have := exp_neg_le (l * x) (mul_nonneg hl (NNReal.coe_nonneg x))
          rw [neg_mul]; nlinarith
    _ = _ := by
        have hA : Integrable (fun x : ℝ≥0 => 1 - l * (x : ℝ)) ρ :=
          (integrable_const _).sub (h1.const_mul _)
        have hB : Integrable (fun x : ℝ≥0 => l * (x : ℝ)) ρ := h1.const_mul _
        have hC : Integrable (fun x : ℝ≥0 => l ^ 2 * (x : ℝ) ^ 2) ρ := h2.const_mul _
        rw [integral_add hA hC, integral_sub (integrable_const _) hB, integral_const_mul,
          integral_const_mul]
        simp

theorem lap_pos_le (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) {s0 : ℝ} (hs0 : 0 < s0)
    (he : Integrable (fun x : ℝ≥0 => Real.exp (s0 * x)) ρ) {s : ℝ} (hs : 0 ≤ s)
    (hss : s ≤ s0 / 2) :
    lap ρ s ≤ 1 + s * ∫ x : ℝ≥0, (x : ℝ) ∂ρ +
      s ^ 2 * (32 / s0 ^ 2 * ∫ x : ℝ≥0, Real.exp (s0 * x) ∂ρ) := by
  unfold lap
  have key : ∀ x : ℝ≥0, Real.exp (s * x) ≤ 1 + s * x + s ^ 2 * (32 / s0 ^ 2 * Real.exp (s0 * x)) := by
    intro x
    have hx := NNReal.coe_nonneg x
    have e1 := exp_le (s * x) (mul_nonneg hs hx)
    have q := Real.quadratic_le_exp_of_nonneg (show 0 ≤ s0 * x / 4 by positivity)
    have hx2 : (x : ℝ) ^ 2 ≤ 32 / s0 ^ 2 * Real.exp (s0 * x / 4) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (s0 * x / 4), Real.exp_pos (s0 * x / 4)]
    have hmono : Real.exp (s0 * x / 4) * Real.exp (s * x) ≤ Real.exp (s0 * x) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
    have : (s * x) ^ 2 * Real.exp (s * x) ≤ s ^ 2 * (32 / s0 ^ 2 * Real.exp (s0 * x)) := by
      rw [mul_pow]
      have : (x : ℝ) ^ 2 * Real.exp (s * x) ≤ 32 / s0 ^ 2 * Real.exp (s0 * x) := by
        calc (x : ℝ) ^ 2 * Real.exp (s * x)
            ≤ 32 / s0 ^ 2 * Real.exp (s0 * x / 4) * Real.exp (s * x) :=
              mul_le_mul_of_nonneg_right hx2 (Real.exp_pos _).le
          _ = 32 / s0 ^ 2 * (Real.exp (s0 * x / 4) * Real.exp (s * x)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by positivity)
      calc s ^ 2 * (x : ℝ) ^ 2 * Real.exp (s * x) = s ^ 2 * ((x : ℝ) ^ 2 * Real.exp (s * x)) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hint : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) ρ := by
    refine (((integrable_const 1).add (h1.const_mul s)).add
      ((he.const_mul (32 / s0 ^ 2)).const_mul (s ^ 2))).mono' (by fun_prop)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact key x
  have hR : Integrable (fun x : ℝ≥0 => 1 + s * (x : ℝ) + s ^ 2 * (32 / s0 ^ 2 *
      Real.exp (s0 * x))) ρ :=
    ((integrable_const 1).add (h1.const_mul s)).add ((he.const_mul _).const_mul _)
  calc ∫ x : ℝ≥0, Real.exp (s * x) ∂ρ ≤ ∫ x : ℝ≥0, (1 + s * (x : ℝ) + s ^ 2 * (32 / s0 ^ 2 *
        Real.exp (s0 * x))) ∂ρ := integral_mono hint hR key
    _ = _ := by
        have hA : Integrable (fun x : ℝ≥0 => 1 + s * (x : ℝ)) ρ :=
          (integrable_const _).add (h1.const_mul _)
        have hB : Integrable (fun x : ℝ≥0 => s * (x : ℝ)) ρ := h1.const_mul _
        have hC : Integrable (fun x : ℝ≥0 => s ^ 2 * (32 / s0 ^ 2 * Real.exp (s0 * x))) ρ :=
          (he.const_mul _).const_mul _
        rw [integral_add hA hC, integral_add (integrable_const _) hB, integral_const_mul,
          integral_const_mul, integral_const_mul]
        simp

end bounds

end PB7N

namespace PB7N
open ProbabilityTheory

section cheb
variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

theorem memLp_coord (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) (i : ℕ) :
    MemLp (fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) 2 (seq ρ) := by
  rw [memLp_two_iff_integrable_sq ((measurable_pi_apply i).coe_nnreal_real.aestronglyMeasurable)]
  have h : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ((seq ρ).map (fun ω => ω i)) := by
    rw [map_eval]; exact h2
  exact (integrable_map_measure h.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h

theorem var_coord (i : ℕ) :
    variance (fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) (seq ρ) = variance (fun x : ℝ≥0 => (x : ℝ)) ρ :=
  (measurePreserving_eval_infinitePi (fun _ => ρ) i).variance_fun_comp (by fun_prop)

theorem mean_S (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (k : ℕ) :
    ∫ ω, S k ω ∂seq ρ = k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ := by
  unfold S
  have hi : ∀ i, Integrable (fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ)) (seq ρ) := by
    intro i
    have h : Integrable (fun x : ℝ≥0 => (x : ℝ)) ((seq ρ).map (fun ω => ω i)) := by
      rw [map_eval]; exact h1
    exact (integrable_map_measure h.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h
  rw [integral_finsetSum _ fun i _ => hi i]
  simp only [integral_coord ρ (fun x : ℝ≥0 => (x : ℝ)) (by fun_prop), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

theorem var_S (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) (k : ℕ) :
    variance (S k) (seq ρ) = k * variance (fun x : ℝ≥0 => (x : ℝ)) ρ := by
  have hS : S k = fun ω => ∑ i ∈ Finset.range k, ((ω i : ℝ≥0) : ℝ) := rfl
  rw [hS, variance_fun_sum' (X := fun i (ω : ℕ → ℝ≥0) => ((ω i : ℝ≥0) : ℝ))
    (fun i _ => memLp_coord ρ h2 i)]
  have : ∀ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
      cov[fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ), fun ω : ℕ → ℝ≥0 => ((ω j : ℝ≥0) : ℝ); seq ρ] =
      variance (fun x : ℝ≥0 => (x : ℝ)) ρ := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [covariance_self ((measurable_pi_apply i).coe_nnreal_real.aemeasurable), var_coord]
    · intro j _ hji
      exact ((indep ρ).indepFun hji.symm).covariance_eq_zero (memLp_coord ρ h2 i)
        (memLp_coord ρ h2 j)
    · intro h; exact absurd hi h
  rw [Finset.sum_congr rfl this]
  simp

/-- Chebyshev upper-tail bound for i.i.d. sums. -/
theorem cheb (h1 : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ)
    (h2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) ρ) (k : ℕ) (y : ℝ)
    (hy : k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ < y) :
    (seq ρ).real {ω | y ≤ S k ω} ≤
      k * variance (fun x : ℝ≥0 => (x : ℝ)) ρ / (y - k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ) ^ 2 := by
  set c := y - k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ
  have hc : 0 < c := by simp only [c]; linarith
  have hmem : MemLp (S k) 2 (seq ρ) := by
    have : S k = ∑ i ∈ Finset.range k, fun ω : ℕ → ℝ≥0 => ((ω i : ℝ≥0) : ℝ) := by
      ext ω; simp [S]
    rw [this]; exact memLp_finsetSum' _ fun i _ => memLp_coord ρ h2 i
  have hcheb := meas_ge_le_variance_div_sq hmem hc
  rw [mean_S ρ h1, var_S ρ h2] at hcheb
  have hsub : {ω | y ≤ S k ω} ⊆ {ω | c ≤ |S k ω - k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [abs_of_nonneg (by simp only [c] at hc ⊢; linarith)]
    simp only [c]; linarith
  have hv : 0 ≤ (k : ℝ) * variance (fun x : ℝ≥0 => (x : ℝ)) ρ / c ^ 2 := by
    have := variance_nonneg (fun x : ℝ≥0 => (x : ℝ)) ρ; positivity
  calc (seq ρ).real {ω | y ≤ S k ω}
      ≤ (seq ρ).real {ω | c ≤ |S k ω - k * ∫ x : ℝ≥0, (x : ℝ) ∂ρ|} := measureReal_mono hsub
    _ ≤ _ := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal hv hcheb

end cheb
end PB7N

namespace PB7N
open PerishBaseStock.Backlog

theorem rc_ge (n : ℕ) (hn : 1 ≤ n) (x : ℕ → ℝ≥0) (K : ℕ)
    (h : S K x ≤ n) : (K : ℕ∞) ≤ renewalCount n x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold renewalCount
  refine le_iSup₂_of_le K ?_ le_rfl
  rw [div_le_one hn']; exact h

theorem S_mono (x : ℕ → ℝ≥0) {a b : ℕ} (hab : a ≤ b) : S a x ≤ S b x := by
  unfold S
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    fun _ _ _ => NNReal.coe_nonneg _

theorem rc_le (n : ℕ) (hn : 1 ≤ n) (x : ℕ → ℝ≥0) (k : ℕ)
    (h : (n : ℝ) < S (k + 1) x) : renewalCount n x ≤ k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold renewalCount
  refine iSup₂_le fun N hN => ?_
  rw [div_le_one hn'] at hN
  have : N ≤ k := by
    by_contra hc
    push Not at hc
    have := S_mono x (show k + 1 ≤ N by omega)
    unfold S at this h; linarith
  exact_mod_cast this

theorem rc_top (n : ℕ) (hn : 1 ≤ n) (x : ℕ → ℝ≥0) (h : renewalCount n x = ⊤) (K : ℕ) :
    S K x ≤ n := by
  rcases K with _ | k
  · simp [S]
  · by_contra hc
    push Not at hc
    have := rc_le n hn x k hc
    rw [h] at this
    exact absurd this (by simp)

theorem popDemand_le (n : ℕ) (ω : PerishBaseStock.Population.PopSample) (k : ℕ)
    (h : renewalCount n ω.2 ≤ k) : ((popDemand n ω : ℝ≥0) : ℝ) ≤ S k ω.1 := by
  unfold popDemand
  have hT : (∑' j : ℕ, if ((j + 1 : ℕ) : ℕ∞) ≤ renewalCount n ω.2 then (ω.1 j : ℝ≥0∞) else 0) ≤
      ∑ j ∈ Finset.range k, (ω.1 j : ℝ≥0∞) := by
    calc _ ≤ ∑' j : ℕ, (if j < k then (ω.1 j : ℝ≥0∞) else 0) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          split_ifs with hj hj'
          · exact le_rfl
          · exfalso; have := hj.trans h; norm_cast at this
          · exact bot_le
          · exact le_rfl
      _ = _ := by
          rw [tsum_eq_sum (s := Finset.range k)]
          · exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.1 hj)]
          · intro j hj; rw [if_neg (by simpa using hj)]
  have hfin : (∑ j ∈ Finset.range k, (ω.1 j : ℝ≥0∞)) ≠ ⊤ := by
    rw [← ENNReal.ofNNReal_finsetSum]; exact ENNReal.coe_ne_top
  have := ENNReal.toNNReal_mono hfin hT
  rw [← ENNReal.ofNNReal_finsetSum, ENNReal.toNNReal_coe] at this
  unfold S
  rw [← NNReal.coe_sum]
  exact_mod_cast this

theorem popDemand_ge (n : ℕ) (ω : PerishBaseStock.Population.PopSample) (k : ℕ)
    (hk : (k : ℕ∞) ≤ renewalCount n ω.2) (hfin : renewalCount n ω.2 ≠ ⊤) :
    S k ω.1 ≤ ((popDemand n ω : ℝ≥0) : ℝ) := by
  obtain ⟨N0, hN0⟩ := ENat.ne_top_iff_exists.1 hfin
  have hkN : k ≤ N0 := by rw [← hN0] at hk; exact_mod_cast hk
  unfold popDemand
  have hT : (∑' j : ℕ, if ((j + 1 : ℕ) : ℕ∞) ≤ renewalCount n ω.2 then (ω.1 j : ℝ≥0∞) else 0) =
      ∑ j ∈ Finset.range N0, (ω.1 j : ℝ≥0∞) := by
    rw [tsum_eq_sum (s := Finset.range N0)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_pos]; rw [← hN0]; simp at hj; exact_mod_cast hj
    · intro j hj
      rw [if_neg]; rw [← hN0]; simp at hj; norm_cast; omega
  rw [hT, ← ENNReal.ofNNReal_finsetSum, ENNReal.toNNReal_coe, NNReal.coe_sum]
  exact S_mono ω.1 hkN

end PB7N

namespace PB7N
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H ProbabilityTheory

/-- If `(h+b) P(X_{L+1} ≤ S₁) > b`, every minimizer of `C̃^L` is at most `S₁`. -/
theorem level_le (P : DemandLaw) (c : Params) (hc : c.Standing) (S S1 : ℝ≥0)
    (hS : IsHeuristicLevel P c S)
    (hp : c.b < (c.h + c.b) * (leadTimeLaw P c.L).real (Set.Iic S1)) : S ≤ S1 := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  by_contra hlt
  push Not at hlt
  have hlt' : (S1 : ℝ) < S := hlt
  set μ := leadTimeLaw P c.L
  set p := μ.real (Set.Iic S1)
  have hi := lead_integrable P c.L
  have hmin := hS S1
  unfold heuristicCost at hmin
  -- holding part
  have hH : (S - (S1 : ℝ)) * p ≤ expectedHolding μ S - expectedHolding μ S1 := by
    unfold expectedHolding
    rw [← integral_sub (eh_int μ S) (eh_int μ S1)]
    have : (S - (S1 : ℝ)) * p = ∫ x, (Set.Iic S1).indicator (fun _ => (S : ℝ) - S1) x ∂μ := by
      rw [integral_indicator_const _ measurableSet_Iic]; simp [p, smul_eq_mul, mul_comm]
    rw [this]
    refine integral_mono ((integrable_const _).indicator measurableSet_Iic)
      ((eh_int μ S).sub (eh_int μ S1)) fun x => ?_
    by_cases hx : x ∈ Set.Iic S1
    · rw [Set.indicator_of_mem hx]
      have : (x : ℝ) ≤ S1 := hx
      simp only
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [Set.indicator_of_notMem hx]
      simp only
      have h1 : max ((S1 : ℝ) - x) 0 ≤ max ((S : ℝ) - x) 0 := max_le_max (by linarith) le_rfl
      linarith
  -- shortage part
  have hB : -(S - (S1 : ℝ)) + (S - (S1 : ℝ)) * p ≤
      expectedShortfall μ S - expectedShortfall μ S1 := by
    unfold expectedShortfall
    rw [← integral_sub (es_int μ hi S) (es_int μ hi S1)]
    have : -(S - (S1 : ℝ)) + (S - (S1 : ℝ)) * p = ∫ x, (-(S - (S1 : ℝ)) +
        (Set.Iic S1).indicator (fun _ => (S : ℝ) - S1) x) ∂μ := by
      rw [integral_add (integrable_const _) ((integrable_const _).indicator measurableSet_Iic),
        integral_indicator_const _ measurableSet_Iic]
      simp [p, smul_eq_mul, mul_comm]
    rw [this]
    refine integral_mono ((integrable_const _).add ((integrable_const _).indicator
      measurableSet_Iic)) ((es_int μ hi S).sub (es_int μ hi S1)) fun x => ?_
    by_cases hx : x ∈ Set.Iic S1
    · rw [Set.indicator_of_mem hx]
      have : (x : ℝ) ≤ S1 := hx
      simp only
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
    · rw [Set.indicator_of_notMem hx]
      simp only
      rcases le_total ((x : ℝ) - S) 0 with h1 | h1 <;>
        rcases le_total ((x : ℝ) - S1) 0 with h2 | h2 <;>
        simp only [max_eq_right h1, max_eq_left h1, max_eq_right h2, max_eq_left h2] <;>
        linarith
  have hL0 : (0 : ℝ) ≤ c.L := Nat.cast_nonneg _
  have hmr : (1 : ℝ) ≤ c.m := by exact_mod_cast hm1
  have hα : 0 ≤ (c.θ - c.h * c.L) / ((c.m : ℝ) + c.L) := div_nonneg (by linarith) (by positivity)
  have h3 := mul_le_mul_of_nonneg_left
    (eh_mono (leadTimeLaw P (c.m + c.L - 1)) hlt.le) hα
  have hpos : 0 < (S - (S1 : ℝ)) * ((c.h + c.b) * p - c.b) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hH hh.le, mul_le_mul_of_nonneg_left hB hb.le]

/-- Union bound: `P(X_A > A y) ≤ A · P(D > y)`. -/
theorem lead_Iic_ge (P : DemandLaw) (k : ℕ) (y : ℝ≥0) :
    1 - (k + 1) * P.law.real {x | y < x} ≤
      (leadTimeLaw P k).real (Set.Iic ((k + 1 : ℕ) * y)) := by
  have hm := meas_sum k
  set ν := demandPathLaw P
  have hsub : {d : DemandPath | (k + 1 : ℕ) * y < ∑ i ∈ Finset.range (k + 1), d i} ⊆
      ⋃ i ∈ Finset.range (k + 1), {d : DemandPath | y < d i} := by
    intro d hd
    simp only [Set.mem_setOf_eq] at hd
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hcon
    have : ∑ i ∈ Finset.range (k + 1), d i ≤ ∑ i ∈ Finset.range (k + 1), y :=
      Finset.sum_le_sum fun i hi => hcon i hi
    simp at this
    exact absurd hd (not_lt.2 (by simpa using this))
  have hcoord : ∀ i, ν {d : DemandPath | y < d i} = P.law {x | y < x} := by
    intro i
    change ν ((fun d : DemandPath => d i) ⁻¹' Set.Ioi y) = P.law (Set.Ioi y)
    rw [← Measure.map_apply (measurable_pi_apply i) measurableSet_Ioi]
    unfold ν demandPathLaw; rw [Measure.infinitePi_map_eval]
  have hU : ν {d : DemandPath | (k + 1 : ℕ) * y < ∑ i ∈ Finset.range (k + 1), d i} ≤
      (k + 1 : ℕ) * P.law {x | y < x} := by
    calc _ ≤ ν (⋃ i ∈ Finset.range (k + 1), {d : DemandPath | y < d i}) := measure_mono hsub
      _ ≤ ∑ i ∈ Finset.range (k + 1), ν {d : DemandPath | y < d i} := measure_biUnion_finset_le _ _
      _ = _ := by simp [hcoord]
  have hcompl : (leadTimeLaw P k).real (Set.Iic ((k + 1 : ℕ) * y)) =
      1 - ν.real {d : DemandPath | (k + 1 : ℕ) * y < ∑ i ∈ Finset.range (k + 1), d i} := by
    unfold leadTimeLaw
    rw [map_measureReal_apply hm measurableSet_Iic]
    have : (fun d : DemandPath => ∑ i ∈ Finset.range (k + 1), d i) ⁻¹' Set.Iic ((k + 1 : ℕ) * y) =
        {d : DemandPath | (k + 1 : ℕ) * y < ∑ i ∈ Finset.range (k + 1), d i}ᶜ := by
      ext d; simp
    rw [this, probReal_compl_eq_one_sub (measurableSet_lt measurable_const hm)]
  rw [hcompl]
  have : ν.real {d : DemandPath | (k + 1 : ℕ) * y < ∑ i ∈ Finset.range (k + 1), d i} ≤
      (k + 1) * P.law.real {x | y < x} := by
    have h := ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hU
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
    push_cast at h
    simpa [measureReal_def] using h
  linarith

/-- Generalized Chernoff tail bound for `H`: `E[(S - Σ_{i<k} D_i)^+] ≤ S e^{lS} (E e^{-lD})^k`. -/
theorem tail_bound_l (P : DemandLaw) (k : ℕ) (S : ℝ≥0) {l : ℝ} (hl : 0 ≤ l) :
    expectedHolding (leadTimeLaw P k) S ≤
      (S : ℝ) * Real.exp (l * S) * lap P.law (-l) ^ (k + 1) := by
  rw [PB7E.eh_as]
  have hmg := mgf_S P.law (k + 1) (-l)
  rw [← hmg]
  unfold mgf
  rw [← integral_const_mul]
  have hint := integrable_exp_neg P.law (k + 1) hl
  have hint2 : Integrable (fun d : DemandPath =>
      max ((S : ℝ) - ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ)) 0) (demandPathLaw P) := by
    refine Integrable.of_bound ((measurable_const.sub (PB7E.meas_sumR _)).max
      measurable_const).aestronglyMeasurable (S : ℝ) (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ) :=
      Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
    exact max_le (by linarith) S.2
  refine integral_mono hint2 (hint.const_mul _) fun d => ?_
  simp only [PB7N.S]
  set y := ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ)
  have hS : (0 : ℝ) ≤ S := S.2
  rcases le_total ((S : ℝ) - y) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h]
    have e : Real.exp (l * S) * Real.exp (-l * y) = Real.exp (l * (S - y)) := by
      rw [← Real.exp_add]; ring_nf
    rw [mul_assoc, e]
    have : 1 ≤ Real.exp (l * ((S : ℝ) - y)) := Real.one_le_exp (mul_nonneg hl h)
    have hy : 0 ≤ y := Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
    nlinarith

end PB7N

namespace PB7N
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H ProbabilityTheory

section pop
variable (M : PopulationModel)

theorem popLaw_eq : popLaw M = (seq M.lawHat).prod (seq M.lawX) := rfl

instance : IsProbabilityMeasure (popLaw M) := by rw [popLaw_eq]; infer_instance

theorem mp_fst : MeasurePreserving Prod.fst (popLaw M) (seq M.lawHat) := by
  rw [popLaw_eq]; exact measurePreserving_fst

theorem mp_snd : MeasurePreserving Prod.snd (popLaw M) (seq M.lawX) := by
  rw [popLaw_eq]; exact measurePreserving_snd

theorem aem_pop (n : ℕ) (h : IsProbabilityMeasure (popDemandLaw M n)) :
    AEMeasurable (popDemand n) (popLaw M) := by
  by_contra hc
  unfold popDemandLaw at h
  rw [Measure.map_of_not_aemeasurable hc] at h
  have h1 : (0 : Measure ℝ≥0) Set.univ = 1 := h.measure_univ
  rw [Measure.coe_zero, Pi.zero_apply] at h1
  exact zero_ne_one h1

theorem snd_real (A : Set (ℕ → ℝ≥0)) (hA : MeasurableSet A) :
    (popLaw M).real (Prod.snd ⁻¹' A) = (seq M.lawX).real A := by
  rw [← map_measureReal_apply measurable_snd hA, (mp_snd M).map_eq]

theorem fst_real (A : Set (ℕ → ℝ≥0)) (hA : MeasurableSet A) :
    (popLaw M).real (Prod.fst ⁻¹' A) = (seq M.lawHat).real A := by
  rw [← map_measureReal_apply measurable_fst hA, (mp_fst M).map_eq]

/-- `lap X (-l) < 1` for a small `l > 0`. -/
theorem lapX_lt_one : ∃ l : ℝ, 0 < l ∧ lap M.lawX (-l) < 1 ∧ 0 ≤ lap M.lawX (-l) := by
  set xm2 := ∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂M.lawX
  have hxm2 : 0 ≤ xm2 := integral_nonneg fun y => sq_nonneg _
  set l := 1 / (2 * (xm2 + 1))
  have hl : 0 < l := by positivity
  refine ⟨l, hl, ?_, integral_nonneg fun _ => (Real.exp_pos _).le⟩
  have h := lap_neg_le M.lawX M.xIntegrable M.xVar hl.le
  rw [M.xMeanOne] at h
  have : l * xm2 ≤ 1 / 2 := by
    simp only [l]; rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

theorem N_top_null (n : ℕ) (hn : 1 ≤ n) :
    popLaw M {ω | renewalCount n ω.2 = ⊤} = 0 := by
  obtain ⟨l, hl, hq1, hq0⟩ := lapX_lt_one M
  have hbound : ∀ K : ℕ, popLaw M {ω | renewalCount n ω.2 = ⊤} ≤
      ENNReal.ofReal (Real.exp (l * n) * lap M.lawX (-l) ^ K) := by
    intro K
    have hsub : {ω : PerishBaseStock.Population.PopSample | renewalCount n ω.2 = ⊤} ⊆
        Prod.snd ⁻¹' {x | S K x ≤ n} := fun ω hω => rc_top n hn ω.2 hω K
    have hmeas : MeasurableSet {x : ℕ → ℝ≥0 | S K x ≤ n} := measurableSet_le (meas_S K) measurable_const
    calc _ ≤ popLaw M (Prod.snd ⁻¹' {x | S K x ≤ n}) := measure_mono hsub
      _ = ENNReal.ofReal ((popLaw M).real (Prod.snd ⁻¹' {x | S K x ≤ n})) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ _ := by
          rw [snd_real M _ hmeas]
          exact ENNReal.ofReal_le_ofReal (lower_tail M.lawX K n hl.le)
  have ht : Tendsto (fun K : ℕ => ENNReal.ofReal (Real.exp (l * n) * lap M.lawX (-l) ^ K))
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (Real.exp (l * n))
  exact le_antisymm (ge_of_tendsto' ht hbound) bot_le

/-- Laplace transform bound for one period's demand of form (7). -/
theorem lap_pop_le (n : ℕ) (hn : 1 ≤ n) (hP : IsProbabilityMeasure (popDemandLaw M n))
    (k : ℕ) {l : ℝ} (hl : 0 ≤ l) :
    ∫ ω, Real.exp (-l * (popDemand n ω : ℝ)) ∂popLaw M ≤
      (seq M.lawX).real {x | (n : ℝ) ≤ S k x} + lap M.lawHat (-l) ^ k := by
  have haem := aem_pop M n hP
  have hmeasA : MeasurableSet {x : ℕ → ℝ≥0 | (n : ℝ) ≤ S k x} :=
    measurableSet_le measurable_const (meas_S k)
  set A : Set PerishBaseStock.Population.PopSample := Prod.snd ⁻¹' {x : ℕ → ℝ≥0 | (n : ℝ) ≤ S k x}
  have hA : MeasurableSet A := measurable_snd hmeasA
  have hint1 : Integrable (fun ω : PerishBaseStock.Population.PopSample =>
      Real.exp (-l * (popDemand n ω : ℝ))) (popLaw M) := by
    refine Integrable.of_bound (by
      exact (Real.continuous_exp.comp_aestronglyMeasurable
        ((haem.coe_nnreal_real.const_mul (-l)).aestronglyMeasurable))) 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [NNReal.coe_nonneg (popDemand n ω)])
  have hint2 : Integrable (fun ω : PerishBaseStock.Population.PopSample =>
      Real.exp (-l * S k ω.1)) (popLaw M) := by
    have := integrable_exp_neg M.lawHat k hl
    rw [← (mp_fst M).map_eq] at this
    exact (integrable_map_measure this.aestronglyMeasurable measurable_fst.aemeasurable).1 this
  have hintR : Integrable (fun ω : PerishBaseStock.Population.PopSample =>
      A.indicator (fun _ => (1 : ℝ)) ω + Real.exp (-l * S k ω.1)) (popLaw M) :=
    ((integrable_const _).indicator hA).add hint2
  have hae : ∀ᵐ ω ∂popLaw M, renewalCount n ω.2 ≠ ⊤ := by
    rw [ae_iff]; simpa using N_top_null M n hn
  calc ∫ ω, Real.exp (-l * (popDemand n ω : ℝ)) ∂popLaw M
      ≤ ∫ ω, (A.indicator (fun _ => (1 : ℝ)) ω + Real.exp (-l * S k ω.1)) ∂popLaw M := by
        refine integral_mono_ae hint1 hintR ?_
        filter_upwards [hae] with ω hω
        by_cases hωA : ω ∈ A
        · rw [Set.indicator_of_mem hωA]
          have : Real.exp (-l * (popDemand n ω : ℝ)) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [NNReal.coe_nonneg (popDemand n ω)])
          linarith [Real.exp_pos (-l * S k ω.1)]
        · rw [Set.indicator_of_notMem hωA, zero_add]
          have hle : S k ω.2 ≤ n := by
            simp only [A, Set.mem_preimage, Set.mem_ofPred_eq, not_le] at hωA; linarith
          have hge := popDemand_ge n ω k (rc_ge n hn ω.2 k hle) hω
          exact Real.exp_le_exp.2 (by nlinarith)
    _ = (popLaw M).real A + ∫ ω, Real.exp (-l * S k ω.1) ∂popLaw M := by
        rw [integral_add ((integrable_const _).indicator hA) hint2,
          integral_indicator_const _ hA]
        simp
    _ = _ := by
        rw [snd_real M _ hmeasA]
        congr 1
        have : ∫ ω, Real.exp (-l * S k ω.1) ∂popLaw M =
            ∫ x, Real.exp (-l * S k x) ∂(popLaw M).map Prod.fst := by
          rw [integral_map measurable_fst.aemeasurable
            ((meas_S k).const_mul _).exp.aestronglyMeasurable]
        rw [this, (mp_fst M).map_eq, ← mgf_S]
        rfl

/-- Upper-deviation decomposition: `P(D(n) > y) ≤ P(Σ_{j≤k} X_j ≤ n) + P(Σ_{j<k} D̂_j ≥ y)`. -/
theorem pop_upper (n : ℕ) (hn : 1 ≤ n) (hP : IsProbabilityMeasure (popDemandLaw M n))
    (k : ℕ) (y : ℝ≥0) :
    (popDemandLaw M n).real {x | y < x} ≤
      (seq M.lawX).real {x | S (k + 1) x ≤ n} + (seq M.lawHat).real {x | (y : ℝ) ≤ S k x} := by
  have haem := aem_pop M n hP
  have hm1 : MeasurableSet {x : ℕ → ℝ≥0 | S (k + 1) x ≤ n} :=
    measurableSet_le (meas_S _) measurable_const
  have hm2 : MeasurableSet {x : ℕ → ℝ≥0 | (y : ℝ) ≤ S k x} :=
    measurableSet_le measurable_const (meas_S k)
  have hsub : popDemand n ⁻¹' {x | y < x} ⊆
      Prod.snd ⁻¹' {x | S (k + 1) x ≤ n} ∪ Prod.fst ⁻¹' {x | (y : ℝ) ≤ S k x} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_cases h : S (k + 1) ω.2 ≤ n
    · exact Or.inl h
    · right
      push Not at h
      have := popDemand_le n ω k (rc_le n hn ω.2 k h)
      have hy : (y : ℝ) < popDemand n ω := hω
      linarith
  unfold popDemandLaw
  change (Measure.map (popDemand n) (popLaw M)).real (Set.Ioi y) ≤ _
  rw [map_measureReal_apply_of_aemeasurable haem measurableSet_Ioi]
  calc (popLaw M).real (popDemand n ⁻¹' Set.Ioi y)
      ≤ (popLaw M).real (Prod.snd ⁻¹' {x | S (k + 1) x ≤ n} ∪
          Prod.fst ⁻¹' {x | (y : ℝ) ≤ S k x}) := measureReal_mono hsub
    _ ≤ (popLaw M).real (Prod.snd ⁻¹' {x | S (k + 1) x ≤ n}) +
          (popLaw M).real (Prod.fst ⁻¹' {x | (y : ℝ) ≤ S k x}) := measureReal_union_le _ _
    _ = _ := by rw [snd_real M _ hm1, fst_real M _ hm2]

theorem lap_law_eq (n : ℕ) (hP : IsProbabilityMeasure (popDemandLaw M n)) (l : ℝ) :
    lap (popDemandLaw M n) (-l) = ∫ ω, Real.exp (-l * (popDemand n ω : ℝ)) ∂popLaw M := by
  unfold lap popDemandLaw
  rw [integral_map (aem_pop M n hP) (by fun_prop)]

end pop
end PB7N

namespace PB7N
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H ProbabilityTheory

theorem exp_mul_nat (x : ℝ) (k : ℕ) : Real.exp (x * k) = Real.exp x ^ k := by
  rw [← Real.exp_nat_mul, mul_comm]

section est
variable (M : PopulationModel)

/-- explicit upper-deviation bound for one period -/
theorem upper_dev (n : ℕ) (hn : 1 ≤ n) (hP : IsProbabilityMeasure (popDemandLaw M n))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a : ℝ) (ha : a = ∫ y : ℝ≥0, (y : ℝ) ∂M.lawHat)
    (y : ℝ≥0) (hyv : (y : ℝ) = (1 + δ) * n * a)
    (c1 : ℝ) (hc1 : c1 = δ / (8 * ((∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂M.lawX) + 1)) * δ / 4)
    (C2 : ℝ) (hC2 : C2 = 4 * (1 + δ / 2) * variance (fun x : ℝ≥0 => (x : ℝ)) M.lawHat /
        (δ ^ 2 * a ^ 2)) :
    (popDemandLaw M n).real {x | y < x} ≤ Real.exp (-c1 * n) + C2 / n := by
  have hapos : 0 < a := by rw [ha]; exact M.hatMeanPos
  set xm2 := ∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂M.lawX
  have hxm2 : 0 ≤ xm2 := integral_nonneg fun y => sq_nonneg _
  set l1 := δ / (8 * (xm2 + 1)) with hl1
  have hl1pos : 0 < l1 := by positivity
  have hl1x : l1 * xm2 ≤ δ / 8 := by
    rw [hl1, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set v := variance (fun x : ℝ≥0 => (x : ℝ)) M.lawHat
  have hv : 0 ≤ v := variance_nonneg _ _
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set k := ⌊(1 + δ / 2) * (n : ℝ)⌋₊ with hk
  have hk1 : (k : ℝ) ≤ (1 + δ / 2) * n := Nat.floor_le (by positivity)
  have hk2 : (1 + δ / 2) * (n : ℝ) < k + 1 := Nat.lt_floor_add_one _
  have hsplit := pop_upper M n hn hP k y
  refine hsplit.trans (add_le_add ?_ ?_)
  · -- renewal lower deviation
    have hlt := lower_tail M.lawX (k + 1) n hl1pos.le
    have hlap := lap_neg_le M.lawX M.xIntegrable M.xVar hl1pos.le
    rw [M.xMeanOne] at hlap
    have hlap0 : 0 ≤ lap M.lawX (-l1) := integral_nonneg fun _ => (Real.exp_pos _).le
    have hlap2 : lap M.lawX (-l1) ≤ Real.exp (-(l1 * (1 - δ / 8))) := by
      have := Real.add_one_le_exp (-(l1 * (1 - δ / 8)))
      nlinarith
    have hpow : lap M.lawX (-l1) ^ (k + 1) ≤ Real.exp (-(l1 * (1 - δ / 8)) * (k + 1 : ℕ)) := by
      rw [exp_mul_nat]
      exact pow_le_pow_left₀ hlap0 hlap2 _
    refine hlt.trans ?_
    calc Real.exp (l1 * n) * lap M.lawX (-l1) ^ (k + 1)
        ≤ Real.exp (l1 * n) * Real.exp (-(l1 * (1 - δ / 8)) * (k + 1 : ℕ)) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (l1 * n - l1 * (1 - δ / 8) * (k + 1 : ℕ)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          rw [hc1]
          push_cast
          have hq : 1 + δ / 4 ≤ (1 + δ / 2) * (1 - δ / 8) := by nlinarith
          have h8 : 0 ≤ 1 - δ / 8 := by linarith
          have p1 := mul_le_mul_of_nonneg_left hk2.le (mul_nonneg hl1pos.le h8)
          have p2 := mul_le_mul_of_nonneg_left hq (mul_nonneg hl1pos.le (by positivity : (0 : ℝ) ≤ n))
          nlinarith [p1, p2]
  · -- Chebyshev for customer demands
    rw [hyv]
    have hy : (k : ℝ) * (∫ y : ℝ≥0, (y : ℝ) ∂M.lawHat) < (1 + δ) * n * a := by
      rw [← ha]
      have : (k : ℝ) < (1 + δ) * n := by nlinarith
      exact mul_lt_mul_of_pos_right this hapos
    have hc := cheb M.lawHat M.hatMean M.hatVar k ((1 + δ) * n * a) hy
    rw [← ha] at hc
    refine hc.trans ?_
    have hgap : δ / 2 * n * a ≤ (1 + δ) * n * a - k * a := by
      have := mul_le_mul_of_nonneg_right hk1 hapos.le
      nlinarith
    have hgap0 : 0 < δ / 2 * n * a := by positivity
    calc (k : ℝ) * v / ((1 + δ) * n * a - k * a) ^ 2
        ≤ (1 + δ / 2) * n * v / (δ / 2 * n * a) ^ 2 := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hk1 hv) (by positivity)
          exact pow_le_pow_left₀ hgap0.le hgap 2
      _ = _ := by
          rw [hC2]
          field_simp; ring

/-- explicit lower-tail bound for the Laplace transform of one period's demand -/
theorem lap_dev (n : ℕ) (hn : 1 ≤ n) (hP : IsProbabilityMeasure (popDemandLaw M n))
    (δ η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (s0 : ℝ) (hs0 : 0 < s0) (he : Integrable (fun x : ℝ≥0 => Real.exp (s0 * x)) M.lawX)
    (s : ℝ) (hs : 0 < s) (hss : s ≤ s0 / 2)
    (hsC : s * (32 / s0 ^ 2 * ∫ x : ℝ≥0, Real.exp (s0 * x) ∂M.lawX) ≤ δ / 2)
    (l : ℝ) (hl : 0 ≤ l)
    (hlm : l * ∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂M.lawHat ≤ η * ∫ y : ℝ≥0, (y : ℝ) ∂M.lawHat) :
    lap (popDemandLaw M n) (-l) ≤ Real.exp (-(s * δ / 2) * n) +
      Real.exp (l * ∫ y : ℝ≥0, (y : ℝ) ∂M.lawHat) *
        Real.exp (-((1 - δ) * (1 - η) * l * ∫ y : ℝ≥0, (y : ℝ) ∂M.lawHat) * n) := by
  set a := ∫ y : ℝ≥0, (y : ℝ) ∂M.lawHat
  have hapos : 0 < a := M.hatMeanPos
  set m2 := ∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂M.lawHat
  set C := 32 / s0 ^ 2 * ∫ x : ℝ≥0, Real.exp (s0 * x) ∂M.lawX
  have hC : 0 ≤ C := by
    have : 0 ≤ ∫ x : ℝ≥0, Real.exp (s0 * x) ∂M.lawX := integral_nonneg fun x => (Real.exp_pos _).le
    positivity
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set k := ⌊(1 - δ) * (n : ℝ)⌋₊ with hk
  have hk0 : 0 ≤ (1 - δ) * (n : ℝ) := by nlinarith
  have hk1 : (k : ℝ) ≤ (1 - δ) * n := Nat.floor_le hk0
  have hk2 : (1 - δ) * (n : ℝ) - 1 < k := Nat.sub_one_lt_floor _
  rw [lap_law_eq M n hP]
  refine (lap_pop_le M n hn hP k hl).trans (add_le_add ?_ ?_)
  · -- renewal upper deviation
    have hint : Integrable (fun x : ℝ≥0 => Real.exp (s * x)) M.lawX := by
      refine he.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (NNReal.coe_nonneg x))
    have hut := upper_tail M.lawX k n hs.le hint
    have hlap := lap_pos_le M.lawX M.xIntegrable hs0 he hs.le hss
    rw [M.xMeanOne] at hlap
    have hlap0 : 0 ≤ lap M.lawX s := integral_nonneg fun _ => (Real.exp_pos _).le
    have hlap2 : lap M.lawX s ≤ Real.exp (s + s ^ 2 * C) := by
      have := Real.add_one_le_exp (s + s ^ 2 * C); nlinarith
    have hpow : lap M.lawX s ^ k ≤ Real.exp ((s + s ^ 2 * C) * k) := by
      rw [exp_mul_nat]; exact pow_le_pow_left₀ hlap0 hlap2 _
    refine hut.trans ?_
    calc Real.exp (-s * n) * lap M.lawX s ^ k
        ≤ Real.exp (-s * n) * Real.exp ((s + s ^ 2 * C) * k) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (-s * n + (s + s ^ 2 * C) * k) := by rw [← Real.exp_add]
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          have h1 : (s + s ^ 2 * C) * k ≤ (s + s ^ 2 * C) * ((1 - δ) * n) :=
            mul_le_mul_of_nonneg_left hk1 (by positivity)
          have h2 : s ^ 2 * C * ((1 - δ) * n) ≤ s * (δ / 2) * n := by
            have h3 : s * C * ((1 - δ) * n) ≤ δ / 2 * n := by
              calc s * C * ((1 - δ) * n) ≤ δ / 2 * ((1 - δ) * n) :=
                    mul_le_mul_of_nonneg_right hsC hk0
                _ ≤ δ / 2 * n := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    nlinarith [mul_nonneg hδ.le (by positivity : (0 : ℝ) ≤ n)]
            calc s ^ 2 * C * ((1 - δ) * n) = s * (s * C * ((1 - δ) * n)) := by ring
              _ ≤ s * (δ / 2 * n) := mul_le_mul_of_nonneg_left h3 hs.le
              _ = s * (δ / 2) * n := by ring
          linarith [h1, h2]
  · -- customer lower tail
    have hlap := lap_neg_le M.lawHat M.hatMean M.hatVar hl
    have hlap0 : 0 ≤ lap M.lawHat (-l) := integral_nonneg fun _ => (Real.exp_pos _).le
    have hlap2 : lap M.lawHat (-l) ≤ Real.exp (-(l * a * (1 - η))) := by
      have := Real.add_one_le_exp (-(l * a * (1 - η)))
      have : l ^ 2 * m2 ≤ l * (η * a) := by
        have := mul_le_mul_of_nonneg_left hlm hl; nlinarith
      nlinarith
    have hpow : lap M.lawHat (-l) ^ k ≤ Real.exp (-(l * a * (1 - η)) * k) := by
      rw [exp_mul_nat]; exact pow_le_pow_left₀ hlap0 hlap2 _
    refine hpow.trans ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rcases le_total η 1 with hη1 | hη1
    · have hla : 0 ≤ l * a * (1 - η) := by have := mul_nonneg hl hapos.le; nlinarith
      have p := mul_le_mul_of_nonneg_left hk2.le hla
      have hlaη : 0 ≤ l * a * η := by have := mul_nonneg hl hapos.le; nlinarith
      nlinarith [p, hlaη]
    · -- η > 1: the bound `-(l a (1-η)) k` is nonnegative but so is the target
      have hla : l * a * (η - 1) * k ≤ l * a * (η - 1) * ((1 - δ) * n) :=
        mul_le_mul_of_nonneg_left hk1 (by have := mul_nonneg hl hapos.le; nlinarith)
      nlinarith [hla, mul_nonneg hl hapos.le]

end est
end PB7N

namespace PB7N

theorem threshold_eventually (Ar c1 C2 ε : ℝ) (hc1 : 0 < c1) (hε : 0 < ε) :
    ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n → Ar * (Real.exp (-c1 * n) + C2 / n) < ε := by
  have h1 : Tendsto (fun n : ℕ => Real.exp (-c1 * n)) atTop (𝓝 0) := by
    simp_rw [exp_mul_nat]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith))
  have h2 := tendsto_const_div_atTop_nhds_zero_nat C2
  have h3 : Tendsto (fun n : ℕ => Ar * (Real.exp (-c1 * n) + C2 / n)) atTop (𝓝 0) := by
    simpa using (h1.add h2).const_mul Ar
  exact eventually_atTop.1 (h3.eventually (gt_mem_nhds hε))

theorem exponent_arith (Ar Bn δ l a κ : ℝ) (hAr : 1 ≤ Ar) (hBA : Ar + 1 ≤ Bn)
    (hδ : δ = 1 / (8 * (Ar + 1))) (hl : 0 < l) (ha : 0 < a) (hκ : 0 < κ)
    (hlκ : l * (4 * (Ar + 1) * a) ≤ κ) :
    l * (Ar * ((1 + δ) * a)) - Bn * min κ ((1 - δ) * (1 - δ) * l * a) ≤
      -min (l * a / 2) (κ / 2) := by
  have hδA : δ * (Ar + 1) = 1 / 8 := by rw [hδ]; field_simp
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hla : 0 < l * a := mul_pos hl ha
  have hAδ : Ar * δ ≤ 1 / 8 := by nlinarith
  have hX : l * (Ar * ((1 + δ) * a)) = l * a * (Ar + Ar * δ) := by ring
  rw [hX]
  rcases le_total κ ((1 - δ) * (1 - δ) * l * a) with hκr | hκr
  · rw [min_eq_left hκr]
    have hγ : min (l * a / 2) (κ / 2) ≤ κ / 2 := min_le_right _ _
    have h1 : l * a * (Ar + Ar * δ) ≤ l * a * (Ar + 1) := by
      apply mul_le_mul_of_nonneg_left _ hla.le; linarith
    have h2 : l * a * (Ar + 1) ≤ κ / 4 := by nlinarith
    have h3 : κ ≤ Bn * κ := by nlinarith
    linarith
  · rw [min_eq_right hκr]
    have hγ : min (l * a / 2) (κ / 2) ≤ l * a / 2 := min_le_left _ _
    have h1 : Ar + 3 / 4 ≤ Bn * ((1 - δ) * (1 - δ)) := by
      have e : (Ar + 1) * (1 - 2 * δ) = Ar + 3 / 4 := by nlinarith
      have hB0 : 0 ≤ Bn := by linarith
      have : (Ar + 1) * (1 - 2 * δ) ≤ Bn * ((1 - δ) * (1 - δ)) := by
        have h4 : 1 - 2 * δ ≤ (1 - δ) * (1 - δ) := by nlinarith [sq_nonneg δ]
        have h5 : 0 ≤ 1 - 2 * δ := by nlinarith
        calc (Ar + 1) * (1 - 2 * δ) ≤ Bn * (1 - 2 * δ) := mul_le_mul_of_nonneg_right hBA h5
          _ ≤ _ := mul_le_mul_of_nonneg_left h4 hB0
      linarith
    have h2 : l * a * (Ar + 3 / 4) ≤ Bn * ((1 - δ) * (1 - δ) * l * a) := by
      have := mul_le_mul_of_nonneg_left h1 hla.le
      calc l * a * (Ar + 3 / 4) ≤ l * a * (Bn * ((1 - δ) * (1 - δ))) := this
        _ = _ := by ring
    have h3 : l * a * (Ar + Ar * δ) ≤ l * a * (Ar + 1 / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hla.le
    linarith

theorem n_exp_le (γ : ℝ) (hγ : 0 < γ) (n : ℕ) :
    (n : ℝ) * Real.exp (-(γ * n)) ≤ 2 / γ * Real.exp (-(γ / 2 * n)) := by
  have h1 : γ / 2 * n ≤ Real.exp (γ / 2 * n) := by
    have := Real.add_one_le_exp (γ / 2 * n); linarith
  have e : Real.exp (-(γ * n)) = Real.exp (-(γ / 2 * n)) * Real.exp (-(γ / 2 * n)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (γ / 2 * n) * Real.exp (-(γ / 2 * n)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [e]
  have hpos := Real.exp_pos (-(γ / 2 * n))
  have : (n : ℝ) * Real.exp (-(γ / 2 * n)) ≤ 2 / γ := by
    rw [le_div_iff₀ hγ]
    have := mul_le_mul_of_nonneg_right h1 hpos.le
    nlinarith
  calc (n : ℝ) * (Real.exp (-(γ / 2 * n)) * Real.exp (-(γ / 2 * n)))
      = ((n : ℝ) * Real.exp (-(γ / 2 * n))) * Real.exp (-(γ / 2 * n)) := by ring
    _ ≤ 2 / γ * Real.exp (-(γ / 2 * n)) := mul_le_mul_of_nonneg_right this hpos.le

theorem two_exp_le (Λ κ r la : ℝ) (n : ℕ)
    (h : Λ ≤ Real.exp (-κ * n) + Real.exp la * Real.exp (-r * n)) :
    Λ ≤ (1 + Real.exp la) * Real.exp (-(min κ r) * n) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have e1 : Real.exp (-κ * n) ≤ Real.exp (-(min κ r) * n) :=
    Real.exp_le_exp.2 (by have := min_le_left κ r; nlinarith)
  have e2 : Real.exp (-r * n) ≤ Real.exp (-(min κ r) * n) :=
    Real.exp_le_exp.2 (by have := min_le_right κ r; nlinarith)
  have := mul_le_mul_of_nonneg_left e2 (Real.exp_pos la).le
  nlinarith

end PB7N

set_option maxHeartbeats 1000000 in
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic PB7H PB7N ProbabilityTheory in
theorem solution (c : Params) (hc : c.Standing) (hm : 2 ≤ c.m)
    (M : PopulationModel) (Pn : ℕ → CappedBaseStock.DemandLaw)
    (hPn : ∀ n : ℕ, 1 ≤ n → (Pn n).law = popDemandLaw M n) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ K₂ : ℝ, 0 < K₂ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ S : ℝ≥0, IsHeuristicLevel (Pn n) c S →
        expectedHolding (leadTimeLaw (Pn n) (c.m + c.L - 1)) S ≤
          K₁ * Real.exp (-(K₂ * n)) := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  have hcS : c.Standing := ⟨hm1, hh, hb, hθ⟩
  -- constants
  obtain ⟨Ar, hAr⟩ : ∃ Ar : ℝ, Ar = ((c.L + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hAr1 : (1 : ℝ) ≤ Ar := by rw [hAr]; simp
  obtain ⟨Bn, hBn⟩ : ∃ Bn : ℕ, Bn = c.m + c.L := ⟨_, rfl⟩
  have hBA : Ar + 1 ≤ (Bn : ℝ) := by
    have : (2 : ℝ) ≤ c.m := by exact_mod_cast hm
    rw [hAr, hBn]; push_cast; linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (8 * (Ar + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one (by positivity)]; linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ∫ y : ℝ≥0, (y : ℝ) ∂M.lawHat := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; exact M.hatMeanPos
  obtain ⟨m2, hm2⟩ : ∃ m2 : ℝ, m2 = ∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂M.lawHat := ⟨_, rfl⟩
  have hm20 : 0 ≤ m2 := by rw [hm2]; exact integral_nonneg fun y => sq_nonneg _
  obtain ⟨s0, hs0, he⟩ := M.xExpMoment
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 32 / s0 ^ 2 * ∫ x : ℝ≥0, Real.exp (s0 * x) ∂M.lawX := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    have : 0 ≤ ∫ x : ℝ≥0, Real.exp (s0 * x) ∂M.lawX := integral_nonneg fun x => (Real.exp_pos _).le
    rw [hC]; positivity
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min (s0 / 2) (δ / (2 * (C + 1))) := ⟨_, rfl⟩
  have hs0' : 0 < s := by rw [hs]; exact lt_min (by positivity) (by positivity)
  have hss : s ≤ s0 / 2 := by rw [hs]; exact min_le_left _ _
  have hsC : s * C ≤ δ / 2 := by
    have h1 : s ≤ δ / (2 * (C + 1)) := by rw [hs]; exact min_le_right _ _
    have h2 : δ / (2 * (C + 1)) * C ≤ δ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 hC0]
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = s * δ / 2 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = min (δ * a / (m2 + 1)) (κ / (4 * (Ar + 1) * a)) := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; exact lt_min (by positivity) (by positivity)
  have hlm : l * m2 ≤ δ * a := by
    have h1 : l ≤ δ * a / (m2 + 1) := by rw [hl]; exact min_le_left _ _
    have h2 : δ * a / (m2 + 1) * m2 ≤ δ * a := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [mul_pos hδ0 hapos]
    nlinarith [mul_le_mul_of_nonneg_right h1 hm20]
  have hlκ : l * (4 * (Ar + 1) * a) ≤ κ := by
    have h1 : l ≤ κ / (4 * (Ar + 1) * a) := by rw [hl]; exact min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at h1
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = min (l * a / 2) (κ / 2) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; exact lt_min (by positivity) (by positivity)
  -- the threshold
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = δ / (8 * ((∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂M.lawX) + 1)) * δ / 4 :=
    ⟨_, rfl⟩
  have hc10 : 0 < c1 := by
    have : 0 ≤ ∫ y : ℝ≥0, (y : ℝ) ^ 2 ∂M.lawX := integral_nonneg fun y => sq_nonneg _
    rw [hc1]; positivity
  obtain ⟨C2, hC2⟩ : ∃ C2 : ℝ,
      C2 = 4 * (1 + δ / 2) * variance (fun x : ℝ≥0 => (x : ℝ)) M.lawHat / (δ ^ 2 * a ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨N1, hN1⟩ := threshold_eventually Ar c1 C2 (c.h / (c.h + c.b)) hc10 (by positivity)
  refine ⟨Ar * (1 + δ) * a * (1 + Real.exp (l * a)) ^ Bn * (2 / γ) + 1, by positivity,
    γ / 2, by positivity, max 1 N1, fun n hn S hS => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N1 ≤ n := le_trans (le_max_right _ _) hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hP : IsProbabilityMeasure (popDemandLaw M n) := by
    rw [← hPn n hn1]; exact (Pn n).probability
  have hlaw := hPn n hn1
  -- Step 1: the minimizer is below `S₁ = A (1+δ) n a`
  have hy0 : 0 ≤ (1 + δ) * n * a := by positivity
  obtain ⟨y, hyv⟩ : ∃ y : ℝ≥0, (y : ℝ) = (1 + δ) * n * a := ⟨⟨_, hy0⟩, rfl⟩
  obtain ⟨S1, hS1⟩ : ∃ S1 : ℝ≥0, S1 = ((c.L + 1 : ℕ) : ℝ≥0) * y := ⟨_, rfl⟩
  have hS1r : (S1 : ℝ) = Ar * ((1 + δ) * n * a) := by
    rw [hS1, NNReal.coe_mul, hyv, hAr]; push_cast; ring
  have hud := upper_dev M n hn1 hP δ hδ0 hδ1 a ha y hyv c1 hc1 C2 hC2
  have hIic := lead_Iic_ge (Pn n) c.L y
  rw [hlaw, ← hS1] at hIic
  have hun := hN1 n hnN
  have hprob : c.b < (c.h + c.b) * (leadTimeLaw (Pn n) c.L).real (Set.Iic S1) := by
    have hcL : ((c.L : ℝ) + 1) = Ar := by rw [hAr]; push_cast; ring
    have h1 : 1 - Ar * (Real.exp (-c1 * n) + C2 / n) ≤
        (leadTimeLaw (Pn n) c.L).real (Set.Iic S1) := by
      refine le_trans ?_ hIic
      rw [hcL]
      have := mul_le_mul_of_nonneg_left hud (by linarith : (0 : ℝ) ≤ Ar)
      linarith
    have h2 : (c.h + c.b) * (1 - c.h / (c.h + c.b)) = c.b := by field_simp; ring
    have hpos : 0 < c.h + c.b := by linarith
    have h3 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h4 : (c.h + c.b) * (1 - c.h / (c.h + c.b)) <
        (c.h + c.b) * (1 - Ar * (Real.exp (-c1 * n) + C2 / n)) :=
      mul_lt_mul_of_pos_left (by linarith) hpos
    linarith
  have hSle : S ≤ S1 := level_le (Pn n) c hcS S S1 hS hprob
  have hSler : (S : ℝ) ≤ S1 := hSle
  -- Step 2: Chernoff bound for the tail
  have htb := tail_bound_l (Pn n) (c.m + c.L - 1) S hl0.le
  rw [show c.m + c.L - 1 + 1 = Bn by omega] at htb
  have hlap := lap_dev M n hn1 hP δ δ hδ0 hδ1 hδ0 s0 hs0 he s hs0' hss (by rw [← hC]; exact hsC)
    l hl0.le (by rw [← hm2, ← ha]; exact hlm)
  rw [← hlaw, ← ha] at hlap
  have hΛ0 : 0 ≤ lap (Pn n).law (-l) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hΛρ := two_exp_le (lap (Pn n).law (-l)) (s * δ / 2) ((1 - δ) * (1 - δ) * l * a) (l * a) n
    hlap
  rw [← hκ] at hΛρ
  have hkey := exponent_arith Ar Bn δ l a κ hAr1 hBA hδ hl0 hapos hκ0 hlκ
  rw [← hγ] at hkey
  have hbig := n_exp_le γ hγ0 n
  have hn0 : (0 : ℝ) ≤ n := by positivity
  set ρ := min κ ((1 - δ) * (1 - δ) * l * a) with hρ
  set K0 := Ar * (1 + δ) * a * (1 + Real.exp (l * a)) ^ Bn with hK0
  have hK00 : 0 ≤ K0 := by
    have : 0 ≤ Ar := by linarith
    positivity
  calc expectedHolding (leadTimeLaw (Pn n) (c.m + c.L - 1)) S
      ≤ (S : ℝ) * Real.exp (l * S) * lap (Pn n).law (-l) ^ Bn := htb
    _ ≤ (S1 : ℝ) * Real.exp (l * S1) * lap (Pn n).law (-l) ^ Bn := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hΛ0 _)
        exact mul_le_mul hSler (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hSler hl0.le))
          (Real.exp_pos _).le (by rw [hS1r]; have : 0 ≤ Ar := by linarith
                                  positivity)
    _ ≤ (S1 : ℝ) * Real.exp (l * S1) * ((1 + Real.exp (l * a)) * Real.exp (-ρ * n)) ^ Bn := by
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΛ0 hΛρ _)
        rw [hS1r]; have : 0 ≤ Ar := by linarith
        positivity
    _ = K0 * (n * Real.exp ((l * (Ar * ((1 + δ) * a)) - Bn * ρ) * n)) := by
        rw [mul_pow, ← PB7N.exp_mul_nat, hS1r, hK0]
        rw [show (l * (Ar * ((1 + δ) * a)) - Bn * ρ) * n =
          l * (Ar * ((1 + δ) * n * a)) + -ρ * n * Bn by ring, Real.exp_add]
        ring
    _ ≤ K0 * (n * Real.exp (-(γ * n))) := by
        apply mul_le_mul_of_nonneg_left _ hK00
        apply mul_le_mul_of_nonneg_left _ hn0
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_right hkey hn0
        linarith
    _ ≤ K0 * (2 / γ * Real.exp (-(γ / 2 * n))) := mul_le_mul_of_nonneg_left hbig hK00
    _ ≤ _ := by
        have hE := Real.exp_pos (-(γ / 2 * n))
        rw [hK0]
        nlinarith
