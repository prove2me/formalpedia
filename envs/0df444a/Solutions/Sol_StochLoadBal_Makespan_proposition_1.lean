-- Prove2me | solution 1 for StochLoadBal.Makespan.proposition_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:00:01.974034+00:00
-- url     : https://prove2.me/submissions/8a9b7c2b-afb5-42a6-9f72-df13353d047c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding
import Theorems.Thm_StochLoadBal_Makespan_lemma_5
import Theorems.Thm_StochLoadBal_Makespan_effSize_facts

open MeasureTheory ProbabilityTheory StochLoadBal.Makespan

theorem solution :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (m n : ℕ), 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin m → Fin n → Ω → ℝ),
        (∀ i j, Measurable (X i j)) → (∀ i j ω, 0 ≤ X i j ω) →
        (∀ i j, Integrable (X i j) P) → iIndepFun (fun j ω i => X i j ω) P →
        (¬ ∃ y : Fin m → Fin n → ℝ, LPFeasible P X 17 y) →
        ∀ σ : Fin n → Fin m, c₀ < expMakespan P X σ := by
  obtain ⟨c₀, hc₀, h5⟩ := StochLoadBal.Makespan.lemma_5
  refine ⟨c₀, hc₀, ?_⟩
  intro m n hm Ω _ P _ X hmeas hnn hint hind hinf σ
  by_contra hle
  push_neg at hle
  obtain ⟨h3, h4⟩ := h5 m n hm Ω P X hmeas hnn hint hind σ hle
  apply hinf
  refine ⟨fun i j => if σ j = i then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; by_cases h : σ j = i <;> simp [h]
  · intro i k hk _
    unfold zLoad
    apply Finset.sum_nonneg
    intro j _
    have htm : Measurable (fun ω => trunc (X i j ω)) := by
      unfold trunc
      exact Measurable.ite (measurableSet_le (hmeas i j) measurable_const) (hmeas i j)
        measurable_const
    have hb : ∀ ω, 0 ≤ trunc (X i j ω) ∧ trunc (X i j ω) ≤ 1 := by
      intro ω; unfold trunc; split_ifs with h
      · exact ⟨hnn i j ω, h⟩
      · norm_num
    have := ((StochLoadBal.Makespan.effSize_facts P k hk).1 _ htm hb).1
    by_cases h : σ j = i <;> simp [h, this]
  · intro j
    simp
  · rw [Finset.sum_comm]
    refine le_trans (le_of_eq ?_) h3
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  · intro K hK
    have := h4 K hK
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold zLoad
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : σ j = i <;> simp [h]
