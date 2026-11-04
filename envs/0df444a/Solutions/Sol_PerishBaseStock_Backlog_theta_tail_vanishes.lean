-- Prove2me | solution 1 for PerishBaseStock.Backlog.theta_tail_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:35:35.002588+00:00
-- url     : https://prove2.me/submissions/8f861a34-8879-4646-86eb-981461c6b3d9

import Definitions.Def_PerishBaseStock_Backlog_Model

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

open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic PB7H in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sθ : ℝ → ℝ≥0)
    (hS : ∀ θ : ℝ, c.h * c.L ≤ θ → IsHeuristicLevel P { c with θ := θ } (Sθ θ)) :
    Tendsto (fun θ : ℝ => θ * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) (Sθ θ))
      atTop (𝓝 0) := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  set μ1 := leadTimeLaw P c.L with hμ1
  set μ2 := leadTimeLaw P (c.m + c.L - 1) with hμ2
  have hi1 := lead_integrable P c.L
  have hi2 := lead_integrable P (c.m + c.L - 1)
  set G : ℝ≥0 → ℝ := fun S => c.h * expectedHolding μ1 S + c.b * expectedShortfall μ1 S with hG
  set H : ℝ≥0 → ℝ := fun S => expectedHolding μ2 S with hH
  have hL0 : (0 : ℝ) ≤ c.L := Nat.cast_nonneg _
  have hmr : (1 : ℝ) ≤ c.m := by exact_mod_cast hm1
  set ML : ℝ := (c.m : ℝ) + c.L with hML
  have hMLpos : 0 < ML := by positivity
  have hcost : ∀ θ S, heuristicCost P { c with θ := θ } S = G S + (θ - c.h * c.L) / ML * H S := by
    intro θ S; rfl
  have hH0 : ∀ S, 0 ≤ H S := fun S => eh_nonneg μ2 S
  have hG0 : ∀ S, 0 ≤ G S := fun S =>
    add_nonneg (mul_nonneg hh.le (eh_nonneg μ1 S)) (mul_nonneg hb.le (es_nonneg μ1 S))
  -- Step 1: α H(Sθ) ≤ G 0
  have step1 : ∀ θ, c.h * c.L ≤ θ → (θ - c.h * c.L) / ML * H (Sθ θ) ≤ G 0 := by
    intro θ hθ'
    have := hS θ hθ' 0
    rw [hcost, hcost] at this
    have h0 : H 0 = 0 := eh_zero μ2
    rw [h0, mul_zero, add_zero] at this
    linarith [hG0 (Sθ θ)]
  -- Step 2: α H(S) ≤ b (S - S1)^+ whenever H S1 = 0
  have step2 : ∀ θ, c.h * c.L ≤ θ → ∀ S1 : ℝ≥0, H S1 = 0 →
      (θ - c.h * c.L) / ML * H (Sθ θ) ≤ c.b * max (((Sθ θ : ℝ≥0) : ℝ) - S1) 0 := by
    intro θ hθ' S1 hS1
    set S := Sθ θ
    have hmin := hS θ hθ' (min S S1)
    rw [hcost, hcost] at hmin
    have hHm : H (min S S1) = 0 :=
      le_antisymm (hS1 ▸ eh_mono μ2 (min_le_right _ _)) (hH0 _)
    rw [hHm, mul_zero, add_zero] at hmin
    have e1 := eh_lip μ1 S (min S S1)
    have e2 := es_lip μ1 hi1 S (min S S1)
    have e3 : max (((min S S1 : ℝ≥0) : ℝ) - S) 0 = 0 := by
      apply max_eq_right; have : min S S1 ≤ S := min_le_left _ _
      have : ((min S S1 : ℝ≥0) : ℝ) ≤ S := this
      linarith
    have e4 : max ((S : ℝ) - ((min S S1 : ℝ≥0) : ℝ)) 0 = max ((S : ℝ) - S1) 0 := by
      rcases le_total S S1 with h | h
      · rw [min_eq_left h]; have : (S : ℝ) ≤ S1 := h
        simp only [sub_self, max_self]; exact (max_eq_right (by linarith)).symm
      · rw [min_eq_right h]
    rw [e3] at e1; rw [e4] at e2
    have : G (min S S1) - G S ≤ c.b * max ((S : ℝ) - S1) 0 := by
      simp only [hG]
      nlinarith [mul_le_mul_of_nonneg_left e1 hh.le, mul_le_mul_of_nonneg_left e2 hb.le]
    linarith
  -- the zero set of H and its supremum
  set Z : Set ℝ := {s | ∃ S : ℝ≥0, (S : ℝ) = s ∧ H S = 0} with hZ
  have hZ0 : (0 : ℝ) ∈ Z := ⟨0, by simp, eh_zero μ2⟩
  have hZb : BddAbove Z := by
    refine ⟨∫ x : ℝ≥0, (x : ℝ) ∂μ2, ?_⟩
    rintro s ⟨S, rfl, hS0⟩
    have := eh_ge μ2 hi2 S
    simp only [hH] at hS0
    linarith
  set S0 := sSup Z with hS0def
  have hS0nn : 0 ≤ S0 := le_csSup hZb hZ0
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (8 * (c.b + 1) * ML) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨s1, ⟨S1, hS1s, hS1H⟩, hs1⟩ := exists_lt_of_lt_csSup ⟨0, hZ0⟩
    (show S0 - δ < S0 by linarith)
  set S2 : ℝ≥0 := ⟨S0 + δ, by linarith⟩ with hS2
  have hη : 0 < H S2 := by
    rcases (hH0 S2).lt_or_eq with h | h
    · exact h
    · exfalso
      have : S0 + δ ∈ Z := ⟨S2, rfl, h.symm⟩
      have := le_csSup hZb this
      linarith
  set η := H S2
  refine ⟨max (2 * c.h * c.L + 1) (c.h * c.L + G 0 * ML / η + 1), fun θ hθN => ?_⟩
  have hθ1 : 2 * c.h * c.L + 1 ≤ θ := le_trans (le_max_left _ _) hθN
  have hθ2 : c.h * c.L + G 0 * ML / η + 1 ≤ θ := le_trans (le_max_right _ _) hθN
  have hhL : 0 ≤ c.h * c.L := mul_nonneg hh.le hL0
  have hθ' : c.h * c.L ≤ θ := by linarith
  have hθpos : 0 < θ := by linarith
  have hαpos : 0 < θ - c.h * c.L := by linarith
  set α := (θ - c.h * c.L) / ML with hα
  have hαp : 0 < α := div_pos hαpos hMLpos
  -- H(Sθ) < η
  have hHlt : H (Sθ θ) < η := by
    have h1 := step1 θ hθ'
    have hG0' := hG0 0
    have : G 0 < α * η := by
      rw [hα, div_mul_eq_mul_div, lt_div_iff₀ hMLpos]
      have : G 0 * ML / η < θ - c.h * c.L := by linarith
      rw [div_lt_iff₀ hη] at this
      linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_le_mul_of_nonneg_left hcon hαp.le]
  have hSlt : ((Sθ θ : ℝ≥0) : ℝ) < S0 + δ := by
    by_contra hcon
    push_neg at hcon
    have : S2 ≤ Sθ θ := by
      rw [← NNReal.coe_le_coe]
      exact hcon
    have := eh_mono μ2 this
    simp only [hH] at hHlt
    linarith
  have h2 := step2 θ hθ' S1 hS1H
  have hmax : max (((Sθ θ : ℝ≥0) : ℝ) - S1) 0 ≤ 2 * δ :=
    max_le (by rw [hS1s]; linarith) (by linarith)
  have hαH : α * H (Sθ θ) ≤ c.b * (2 * δ) :=
    h2.trans (mul_le_mul_of_nonneg_left hmax hb.le)
  have hθα : θ ≤ 2 * ML * α := by
    rw [hα, mul_div_assoc', le_div_iff₀ hMLpos]
    nlinarith
  have hHn := hH0 (Sθ θ)
  have hbound : θ * H (Sθ θ) ≤ 2 * ML * (c.b * (2 * δ)) := by
    calc θ * H (Sθ θ) ≤ (2 * ML * α) * H (Sθ θ) := mul_le_mul_of_nonneg_right hθα hHn
      _ = 2 * ML * (α * H (Sθ θ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hαH (by positivity)
  have hfin : 2 * ML * (c.b * (2 * δ)) < ε := by
    rw [hδ]
    field_simp
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hθpos.le hHn)]
  exact lt_of_le_of_lt hbound hfin
