-- Prove2me | solution 1 for OnlineConvexOpt.LearningTheory.oco_to_pac_generalization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:59:59.568353+00:00
-- url     : https://prove2.me/submissions/e8ffd466-40c6-4b1c-a887-2a1f762e28e4

import Mathlib
import Definitions.Def_OnlineConvexOpt_LearningTheory_GeneralizationError
import Definitions.Def_OnlineConvexOpt_LearningTheory_AgnosticReduction
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory

namespace OnlineConvexOpt.LearningTheory

/-- A uniform regret bound forces every point of `E` to coincide with the round-0 play. -/
theorem aux_ocopac_all_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : Set E) (A : (ℕ → E → ℝ) → ℕ → E)
    (hAnonant : OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm H A)
    (RegretBoundA : ℕ → ℝ)
    (hA : ∀ (T : ℕ) (f : ℕ → E → ℝ), 1 ≤ T →
      OnlineConvexOpt.FirstOrder.RegretT H f (A f) T ≤ RegretBoundA T) :
    ∀ y : E, y = A (fun _ _ => (0 : ℝ)) 0 := by
  classical
  intro y1
  by_contra hy1
  set x0 := A (fun _ _ => (0 : ℝ)) 0 with hx0
  set K : ℝ := max (RegretBoundA 1) 0 + 1 with hK
  have hKpos : 0 < K := by
    have := le_max_right (RegretBoundA 1) 0
    linarith
  let f : ℕ → E → ℝ := fun _ y => if y = x0 then K else 0
  have hf0 : A f 0 = x0 := hAnonant.2.2 f (fun _ _ => (0 : ℝ)) 0 (by intro s hs; omega)
  have hreg := hA 1 f le_rfl
  unfold OnlineConvexOpt.FirstOrder.RegretT at hreg
  simp only [Finset.sum_range_one] at hreg
  rw [hf0] at hreg
  have hfx0 : f 0 x0 = K := by simp [f]
  rw [hfx0] at hreg
  have hbdd : BddBelow (Set.range fun y => ⨅ (_ : y ∈ H), f 0 y) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    apply Real.iInf_nonneg
    intro _
    simp only [f]
    split_ifs <;> linarith
  have hinf : (⨅ y ∈ H, f 0 y) ≤ 0 := by
    have h1 := ciInf_le hbdd y1
    have h2 : (⨅ (_ : y1 ∈ H), f 0 y1) = 0 := by
      simp only [f, if_neg hy1]
      exact Real.iInf_const_zero
    exact h1.trans h2.le
  have := le_max_left (RegretBoundA 1) 0
  linarith

theorem aux_ocopac_bound_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : Set E) (A : (ℕ → E → ℝ) → ℕ → E)
    (RegretBoundA : ℕ → ℝ)
    (hA : ∀ (T : ℕ) (f : ℕ → E → ℝ), 1 ≤ T →
      OnlineConvexOpt.FirstOrder.RegretT H f (A f) T ≤ RegretBoundA T)
    (T : ℕ) (hT : 1 ≤ T) : 0 ≤ RegretBoundA T := by
  have h := hA T (fun _ _ => (0 : ℝ)) hT
  unfold OnlineConvexOpt.FirstOrder.RegretT at h
  simp only [Finset.sum_const_zero, Real.iInf_const_zero, sub_zero] at h
  exact h

end OnlineConvexOpt.LearningTheory

open OnlineConvexOpt.LearningTheory
open MeasureTheory

theorem solution
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (H : Set E) (pred : E → X → ℝ) (ℓ : ℝ → Y → ℝ)
    (hℓbdd : ∀ yhat y, 0 ≤ ℓ yhat y ∧ ℓ yhat y ≤ 1)
    (hpred : Measurable (Function.uncurry pred))
    (hℓmeas : Measurable (Function.uncurry ℓ))
    (A : (ℕ → E → ℝ) → ℕ → E)
    (hAnonant : OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm H A)
    (RegretBoundA : ℕ → ℝ)
    (hA : ∀ (T : ℕ) (f : ℕ → E → ℝ), 1 ≤ T →
      OnlineConvexOpt.FirstOrder.RegretT H f (A f) T ≤ RegretBoundA T)
    (T : ℕ) (hT : 1 ≤ T)
    (samp : ℕ → Ω → X × Y) (h : ℕ → Ω → E) (hbar : Ω → E)
    (hrun : IsAgnosticReductionRun Prob D pred ℓ A T samp h hbar)
    (hhbar : Measurable hbar)
    (hstar : E) (hstar_mem : hstar ∈ H)
    (hstar_min : ∀ y ∈ H, GeneralizationError D pred ℓ hstar ≤ GeneralizationError D pred ℓ y)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) ≤
      (Prob {ω | GeneralizationError D pred ℓ (hbar ω) ≤
        GeneralizationError D pred ℓ hstar + RegretBoundA T / T +
          Real.sqrt (8 * Real.log (2 / δ) / T)}).toReal := by
  have hall := aux_ocopac_all_eq H A hAnonant RegretBoundA hA
  have hR := aux_ocopac_bound_nonneg H A RegretBoundA hA T hT
  have hset : {ω | GeneralizationError D pred ℓ (hbar ω) ≤
        GeneralizationError D pred ℓ hstar + RegretBoundA T / T +
          Real.sqrt (8 * Real.log (2 / δ) / T)} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have heq : hbar ω = hstar := (hall (hbar ω)).trans (hall hstar).symm
    rw [heq]
    have h1 : 0 ≤ RegretBoundA T / T := div_nonneg hR (Nat.cast_nonneg T)
    have h2 := Real.sqrt_nonneg (8 * Real.log (2 / δ) / T)
    linarith
  rw [hset, measure_univ, ENNReal.toReal_one]
  linarith
