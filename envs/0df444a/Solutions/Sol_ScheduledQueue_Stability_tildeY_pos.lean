-- Prove2me | solution 1 for ScheduledQueue.Stability.tildeY_pos
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:57:52.571273+00:00
-- url     : https://prove2.me/submissions/2b1bf3a4-454f-4a34-b277-2ce96359a98a

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

open ScheduledQueue.Stability in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (¬ ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) →
      ∀ r : ℕ, 0 < P {ω | (r : ℕ∞) < tildeY h ξ 0 ω} := by
  intro hunb r
  set S : Finset ℤ := Finset.Icc 1 ((r : ℤ) + 1)
  set sets : ℤ → Set ℝ := fun j => Ici (((j : ℝ) + 2) * h)
  have hpos : ∀ j ∈ S, 0 < P (ξ j ⁻¹' sets j) := by
    intro j _
    rw [pos_iff_ne_zero]
    intro h0
    have e : P (ξ j ⁻¹' sets j) = P (ξ 0 ⁻¹' sets j) :=
      (hin.identDistrib j).measure_mem_eq measurableSet_Ici
    rw [e] at h0
    apply hunb
    refine ⟨((j : ℝ) + 2) * h, ?_⟩
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [mem_setOf_eq, not_le] at hω
    exact hω.le
  have hinter : P (⋂ j ∈ S, ξ j ⁻¹' sets j) = ∏ j ∈ S, P (ξ j ⁻¹' sets j) :=
    hin.indep.measure_inter_preimage_eq_mul S (fun j _ => measurableSet_Ici)
  have hprod : 0 < P (⋂ j ∈ S, ξ j ⁻¹' sets j) := by
    rw [hinter, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun j hj => (hpos j hj).ne'
  refine lt_of_lt_of_le hprod (measure_mono ?_)
  intro ω hω
  simp only [mem_iInter, mem_preimage, sets, mem_Ici] at hω
  simp only [mem_setOf_eq]
  have hsub : (S : Set ℤ) ⊆ {j : ℤ | 1 ≤ j ∧ (j + 2) * h ≤ max (ξ (((0 : ℕ) : ℤ) + j) ω) 0} := by
    intro j hj
    have hj' := hω j hj
    simp only [S, Finset.coe_Icc, mem_Icc] at hj
    refine ⟨hj.1, ?_⟩
    simp only [Nat.cast_zero, zero_add]
    exact hj'.trans (le_max_left _ _)
  have hcard : (S : Set ℤ).encard = ((r + 1 : ℕ) : ℕ∞) := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    simp [S]
  calc (r : ℕ∞) < ((r + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self r
    _ = (S : Set ℤ).encard := hcard.symm
    _ ≤ tildeY h ξ 0 ω := encard_le_encard hsub
