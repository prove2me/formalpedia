-- Prove2me | solution 1 for RobbinsSeqDesign.OptionalStopping.rejection_prob_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:54:07.415792+00:00
-- url     : https://prove2.me/submissions/1d7e30a0-dc2e-4b17-bcd9-6bae7167eaed

import Mathlib
import Definitions.Def_RobbinsSeqDesign_OptionalStopping_Setup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory RobbinsSeqDesign.OptionalStopping
open scoped NNReal

lemma rso_S_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n : ℕ) :
    P.map (S X n) = gaussianReal 0 n := by
  induction n with
  | zero =>
    have h0 : S X 0 = fun _ => (0 : ℝ) := by
      funext ω; simp [S]
    rw [h0, Measure.map_const]
    simp [gaussianReal_zero_var]
  | succ n ih =>
    have hS : S X (n + 1) = S X n + X n := by
      funext ω; simp [S, Finset.sum_range_succ]
    have hS' : S X n = ∑ j ∈ Finset.range n, X j := by
      funext ω; simp [S]
    have hind : IndepFun (S X n) (X n) P := by
      rw [hS']
      exact hindep.indepFun_finsetSum_of_notMem₀ (fun i => (hlaw i).aemeasurable)
        (by simp)
    rw [hS, gaussianReal_add_gaussianReal_of_indepFun hind ih (hlaw n).map_eq]
    have : ((n + 1 : ℕ) : ℝ≥0) = (n : ℝ≥0) + 1 := by push_cast; rfl
    rw [this, add_zero]

lemma rso_Phi (α : ℝ) : (gaussianReal 0 1).real (Set.Ioi α) = 1 - Phi α := by
  have h1 : (gaussianReal 0 1).real (Set.Iic α) = Phi α := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
    unfold Phi gaussianPDFReal
    rw [← integral_const_mul]
    · simp
    -- (no side goals expected)
  rw [← h1, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n : ℕ) (hn : 1 ≤ n) (α : ℝ) :
    P.real {ω | α * Real.sqrt n < S X n ω} = 1 - Phi α := by
  have hSm : AEMeasurable (S X n) P := by
    have : S X n = ∑ j ∈ Finset.range n, X j := by funext ω; simp [S]
    rw [this]
    exact Finset.aemeasurable_sum _ (fun i _ => (hlaw i).aemeasurable)
  have hS : HasLaw (S X n) (gaussianReal 0 n) P := ⟨hSm, rso_S_map P X hindep hlaw n⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hD := gaussianReal_div_const hS (Real.sqrt n)
  have e1 : (0 : ℝ) / Real.sqrt n = 0 := zero_div _
  have e2 : ((n : ℝ≥0) / NNReal.mk (Real.sqrt n ^ 2) (sq_nonneg _)) = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt hn0.le]
    exact div_self hn0.ne'
  rw [e1, e2] at hD
  have hset : {ω | α * Real.sqrt n < S X n ω} = {ω | α < S X n ω / Real.sqrt n} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lt_div_iff₀ hsq]
  rw [hset, Measure.real, hD.measure_eq (p := fun x => α < x) measurableSet_Ioi]
  have := rso_Phi α
  rw [Measure.real] at this
  exact this
