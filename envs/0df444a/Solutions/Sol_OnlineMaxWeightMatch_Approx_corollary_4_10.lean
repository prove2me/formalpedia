-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.corollary_4_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:14:47.641968+00:00
-- url     : https://prove2.me/submissions/70f43d81-994a-4e36-9708-0ecda115518e

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated
import Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_9
import Theorems.Thm_OnlineMaxWeightMatch_Approx_proposition_2_8

open MeasureTheory ProbabilityTheory

namespace LPMCommon
open OnlineMaxWeightMatch.Approx

variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma cumX_le_one {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) : cumX x i t ≤ 1 := by
  calc cumX x i t ≤ ∑ s, x i s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => hx.nonneg i s)
    _ ≤ 1 := hx.bin_le_one i

lemma cumX_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) : 0 ≤ cumX x i t :=
  Finset.sum_nonneg (fun s _ => hx.nonneg i s)

lemma c_eq : (c : ℝ) = 1 / 100 := rfl

lemma acceptProb_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (i : ι) (t : Fin n) : 0 ≤ acceptProb x i t := by
  unfold acceptProb
  have h1 := cumX_le_one hx i t
  have h0 := cumX_nonneg hx i t
  apply le_min zero_le_one
  apply div_nonneg
  · rw [c_eq]; norm_num
  · rw [c_eq]; nlinarith

lemma acceptProb_le_one (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : acceptProb x i t ≤ 1 :=
  min_le_left _ _

lemma pickWeight_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) (o : Option ι) :
    0 ≤ pickWeight I x t o := by
  cases o with
  | some i => exact div_nonneg (hx.nonneg i t) (I.p_nonneg t)
  | none =>
    simp only [pickWeight]
    rw [← Finset.sum_div, htight t]
    rcases (I.p_nonneg t).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [div_self h.ne']; simp

lemma sum_pickWeight (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n) :
    ∑ o : Option ι, pickWeight I x t o = 1 := by
  rw [Fintype.sum_option]
  simp [pickWeight]

lemma ballWeight_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (t : Fin n) (d : BallDraw ι) :
    0 ≤ ballWeight I x t d := by
  unfold ballWeight
  have hA : 0 ≤ (if d.arrives then I.p t else 1 - I.p t) := by
    split_ifs
    · exact I.p_nonneg t
    · linarith [I.p_le_one t]
  have hC : 0 ≤ ∏ i, (if d.coin i then acceptProb x i t else 1 - acceptProb x i t) := by
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact acceptProb_nonneg hx i t
    · linarith [acceptProb_le_one x i t]
  have := pickWeight_nonneg hx htight t d.firstPick
  have := pickWeight_nonneg hx htight t d.secondPick
  positivity

lemma sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : α → ℝ) (B : β → ℝ) (C : γ → ℝ) (D : δ → ℝ) :
    ∑ d : α × β × γ × δ, A d.1 * B d.2.1 * C d.2.2.1 * D d.2.2.2 =
      (∑ a, A a) * (∑ b, B b) * (∑ c, C c) * (∑ d, D d) := by
  simp only [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

open Classical in
lemma sum_ballWeight (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) (t : Fin n) :
    ∑ d : BallDraw ι, ballWeight I x t d = 1 := by
  have h := sum4 (fun b : Bool => if b then I.p t else 1 - I.p t) (pickWeight I x t)
    (fun f : ι → Bool => ∏ i, if f i then acceptProb x i t else 1 - acceptProb x i t)
    (pickWeight I x t)
  have hcoin : ∑ f : ι → Bool, ∏ i, (if f i then acceptProb x i t else 1 - acceptProb x i t)
      = 1 := by
    have h := Fintype.prod_sum (fun i (b : Bool) =>
      if b then acceptProb x i t else 1 - acceptProb x i t)
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_sub_cancel,
      Finset.prod_const_one] at h
    exact h.symm
  rw [Fintype.sum_bool, sum_pickWeight, hcoin] at h
  simp only [if_true, Bool.false_eq_true, if_false, add_sub_cancel, mul_one] at h
  exact h

lemma outcomeWeight_nonneg {I : RideHailInstance ι n} {x : ι → Fin n → ℝ}
    (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t) (ω : Outcome ι n) :
    0 ≤ outcomeWeight I x ω :=
  Finset.prod_nonneg (fun t _ => ballWeight_nonneg hx htight t (ω t))

lemma sum_outcomeWeight (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) :
    ∑ ω : Outcome ι n, outcomeWeight I x ω = 1 := by
  classical
  unfold outcomeWeight
  have h := Fintype.prod_sum (fun (t : Fin n) (d : BallDraw ι) => ballWeight I x t d)
  simp only [sum_ballWeight, Finset.prod_const_one] at h
  exact h.symm

lemma algMeasure_apply (I : RideHailInstance ι n) (x : ι → Fin n → ℝ)
    (s : Set (Outcome ι n)) :
    algMeasure I x s = ∑ ω, ENNReal.ofReal (outcomeWeight I x ω) * s.indicator 1 ω := by
  classical
  rw [algMeasure, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top), smul_eq_mul]

lemma isProb {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) : IsProbabilityMeasure (algMeasure I x) := by
  constructor
  rw [algMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => outcomeWeight_nonneg hx htight ω),
    sum_outcomeWeight]
  simp

/-- the probability of an event as a finite sum of weights -/
lemma real_apply {I : RideHailInstance ι n} {x : ι → Fin n → ℝ} (hx : LPFeasible I x)
    (htight : ∀ t, ∑ i, x i t = I.p t) (s : Set (Outcome ι n)) [DecidablePred (· ∈ s)] :
    (algMeasure I x).real s = ∑ ω, if ω ∈ s then outcomeWeight I x ω else 0 := by
  rw [measureReal_def, algMeasure_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω ∈ s
    · simp [h, Set.indicator, ENNReal.toReal_ofReal (outcomeWeight_nonneg hx htight ω)]
    · simp [h, Set.indicator]
  · intro ω _
    by_cases h : ω ∈ s <;> simp [h, Set.indicator]

end LPMCommon


open MeasureTheory ProbabilityTheory

open OnlineMaxWeightMatch.Approx in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    (t : Fin n) {i j : ι} (hij : i ≠ j) :
    cov[occupancyEarly x i t, occupancyEarly x j t; algMeasure I x] ≤ 0 := by
  haveI := LPMCommon.isProb hx htight
  have hNA := OnlineMaxWeightMatch.Approx.lemma_4_9 I x hx htight t
  have hmem : ∀ k, MemLp (occupancyEarly x k t) 2 (algMeasure I x) := by
    intro k
    apply MemLp.of_bound (C := 1)
    · exact (Measurable.of_discrete).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      unfold occupancyEarly
      by_cases h : ω ∈ occupiedEarlySet x k t <;> simp [Set.indicator, h]
  exact OnlineMaxWeightMatch.Approx.proposition_2_8 (algMeasure I x)
    (fun k => occupancyEarly x k t) hNA hij (hmem i) (hmem j)
