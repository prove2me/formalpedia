-- Prove2me | solution 1 for StochLoadBal.Makespan.observation_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:08:29.286388+00:00
-- url     : https://prove2.me/submissions/b6d16a8c-feef-4a01-a13e-41e056b8fc5e

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding
import Theorems.Thm_StochLoadBal_Makespan_observation_1
import Theorems.Thm_StochLoadBal_Makespan_effSize_facts
import Theorems.Thm_ShmoysTardos_lp_rounding

open MeasureTheory ProbabilityTheory StochLoadBal.Makespan

/-- Every machine classified by the class loop satisfies `z_i(ℓ_i) ≤ b` at its class. -/
lemma slbo2_classLoop_spec {m n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin m → Fin n → Ω → ℝ) (b : ℝ) (y : Fin m → Fin n → ℝ) :
    ∀ (fuel : ℕ) (L : Finset (Fin m)) (cls : Fin m → ℕ) (i : Fin m),
      classLoop P X b y fuel L cls i = cls i ∨
        zLoad P X y i (classLoop P X b y fuel L cls i) ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro L cls i; left; rfl
  | succ k ih =>
    intro L cls i
    classical
    simp only [classLoop]
    split_ifs with h1 h2
    · left; rfl
    · left; rfl
    · rcases ih (L \ L.filter (fun i => zLoad P X y i L.card ≤ b))
        (fun i => if i ∈ L.filter (fun i => zLoad P X y i L.card ≤ b) then L.card else cls i) i
        with h | h
      · rw [h]
        split_ifs with h3
        · right; exact (Finset.mem_filter.mp h3).2
        · left; rfl
      · right; exact h

theorem solution {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (X i j)) (hnn : ∀ i j ω, 0 ≤ X i j ω)
    (hint : ∀ i j, Integrable (X i j) P)
    (b : ℝ) (hb : 0 ≤ b) (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y) :
    (∀ i, ∑ j, procTime P X b y i j * y i j ≤ b) ∧
    (∑ i, ∑ j, gapCost P X i j * y i j ≤ 2) ∧
    (∀ i j, procTime P X b y i j ≤ 1) ∧
    ∃ σ : Fin n → Fin m, IsRoundingOutput P X b y σ := by
  have hcls := (StochLoadBal.Makespan.observation_1 hm P X b y hy).1
  obtain ⟨hy0, _, hy1, hcost, _⟩ := hy
  -- (10): the GAP loads
  have h10 : ∀ i, ∑ j, procTime P X b y i j * y i j ≤ b := by
    intro i
    rcases slbo2_classLoop_spec P X b y m Finset.univ (fun _ => 0) i with h | h
    · exfalso
      have := (hcls i).1
      unfold machineClass at this
      rw [h] at this
      exact absurd this (by norm_num)
    · exact h
  -- the costs
  have h7 : ∑ i, ∑ j, gapCost P X i j * y i j ≤ 2 := hcost
  -- processing times lie in [0, 1]
  have hp01 : ∀ i j, 0 ≤ procTime P X b y i j ∧ procTime P X b y i j ≤ 1 := by
    intro i j
    have htm : Measurable (fun ω => trunc (X i j ω)) := by
      unfold trunc
      exact Measurable.ite (measurableSet_le (hmeas i j) measurable_const) (hmeas i j)
        measurable_const
    have hbd : ∀ ω, 0 ≤ trunc (X i j ω) ∧ trunc (X i j ω) ≤ 1 := by
      intro ω; unfold trunc; split_ifs with h
      · exact ⟨hnn i j ω, h⟩
      · norm_num
    exact (StochLoadBal.Makespan.effSize_facts P _ (hcls i).1).1 _ htm hbd
  refine ⟨h10, h7, fun i j => (hp01 i j).2, ?_⟩
  obtain ⟨σ, -, hσc, hσl⟩ := ShmoysTardos.lp_rounding (procTime P X b y) (gapCost P X) b 1
    (fun i j => (hp01 i j).1) y hy0 hy1 h10 zero_le_one (fun i j _ => (hp01 i j).2)
  exact ⟨σ, hσc.trans h7, hσl⟩
