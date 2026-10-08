-- Prove2me | solution 1 for PalmQueueing.Loynes.coupling_convergence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:48:19.27865+00:00
-- url     : https://prove2.me/submissions/920d764a-e21f-41f8-aaaf-f0889a7716cc

import Mathlib
import Definitions.Def_PalmQueueing_Loynes_Coupling



namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The coupling inequality in set form: the two trajectory events differ only on `{N > k}`
up to a null set. -/
lemma coupling_abs_le {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Z : ℕ → Ω → E) (N : Ω → ℕ)
    (hN : ∀ᵐ ω ∂P, ∀ n : ℕ, N ω ≤ n → X n ω = Z n ω)
    (k : ℕ) (C : Set (ℕ → E)) :
    |(P {ω | (fun n : ℕ => X (n + k) ω) ∈ C}).toReal
      - (P {ω | (fun n : ℕ => Z (n + k) ω) ∈ C}).toReal| ≤ (P {ω | k < N ω}).toReal := by
  set A := {ω | (fun n : ℕ => X (n + k) ω) ∈ C} with hA
  set B := {ω | (fun n : ℕ => Z (n + k) ω) ∈ C} with hB
  set D := {ω | k < N ω} with hD
  -- the bad set
  set S := {ω | ¬ ∀ n : ℕ, N ω ≤ n → X n ω = Z n ω} with hS
  have hS0 : P S = 0 := by
    rw [ae_iff] at hN
    exact hN
  have key : ∀ ω, ω ∉ D → ω ∉ S → ((fun n : ℕ => X (n + k) ω) = fun n : ℕ => Z (n + k) ω) := by
    intro ω hωD hωS
    simp only [hD, Set.mem_setOf_eq, not_lt] at hωD
    simp only [hS, Set.mem_setOf_eq, not_not] at hωS
    funext n
    exact hωS (n + k) (by omega)
  have hAB : A \ B ⊆ D ∪ S := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    have := key ω hc.1 hc.2
    simp only [hA, hB, Set.mem_diff, Set.mem_setOf_eq] at hω
    rw [this] at hω
    exact hω.2 hω.1
  have hBA : B \ A ⊆ D ∪ S := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    have := key ω hc.1 hc.2
    simp only [hA, hB, Set.mem_diff, Set.mem_setOf_eq] at hω
    rw [← this] at hω
    exact hω.2 hω.1
  have hDS : P (D ∪ S) ≤ P D := by
    calc P (D ∪ S) ≤ P D + P S := measure_union_le _ _
      _ = P D := by rw [hS0, add_zero]
  have h1 : P A ≤ P B + P D := by
    calc P A ≤ P ((A ∩ B) ∪ (A \ B)) := by
          apply measure_mono
          intro ω hω
          by_cases h : ω ∈ B
          · exact Or.inl ⟨hω, h⟩
          · exact Or.inr ⟨hω, h⟩
      _ ≤ P (A ∩ B) + P (A \ B) := measure_union_le _ _
      _ ≤ P B + P D := add_le_add (measure_mono Set.inter_subset_right) ((measure_mono hAB).trans hDS)
  have h2 : P B ≤ P A + P D := by
    calc P B ≤ P ((B ∩ A) ∪ (B \ A)) := by
          apply measure_mono
          intro ω hω
          by_cases h : ω ∈ A
          · exact Or.inl ⟨hω, h⟩
          · exact Or.inr ⟨hω, h⟩
      _ ≤ P (B ∩ A) + P (B \ A) := measure_union_le _ _
      _ ≤ P A + P D := add_le_add (measure_mono Set.inter_subset_right) ((measure_mono hBA).trans hDS)
  have hAfin : P A ≠ ⊤ := measure_ne_top _ _
  have hBfin : P B ≠ ⊤ := measure_ne_top _ _
  have hDfin : P D ≠ ⊤ := measure_ne_top _ _
  have h1' : (P A).toReal ≤ (P B).toReal + (P D).toReal := by
    rw [← ENNReal.toReal_add hBfin hDfin]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hBfin, hDfin⟩) h1
  have h2' : (P B).toReal ≤ (P A).toReal + (P D).toReal := by
    rw [← ENNReal.toReal_add hAfin hDfin]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAfin, hDfin⟩) h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem coupling_convergence_core {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Ω) (X Z : ℕ → Ω → E)
    (hXmeas : ∀ n, Measurable (X n)) (hZmeas : ∀ n, Measurable (Z n))
    (hZcomp : IsShiftCompatible θ Z)
    (hcouple : Couple P X Z) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ C : Set (ℕ → E), MeasurableSet C →
        |(P {ω | (fun n : ℕ => X (n + k) ω) ∈ C}).toReal
          - (P {ω | (fun n : ℕ => Z (n + k) ω) ∈ C}).toReal| ≤ ε := by
  intro ε hε
  obtain ⟨N, hNmeas, hN⟩ := hcouple
  -- P {N > k} → 0
  have hanti : Antitone (fun k : ℕ => {ω | k < N ω}) := by
    intro a b hab ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    omega
  have hinter : (⋂ k : ℕ, {ω | k < N ω}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    exact ⟨N ω, le_rfl⟩
  have htend : Tendsto (fun k : ℕ => P {ω | k < N ω}) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) (s := fun k : ℕ => {ω | k < N ω})
      (fun k => (measurableSet_lt measurable_const hNmeas).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at this
    exact this
  have hev : ∀ᶠ k in atTop, P {ω | k < N ω} < ENNReal.ofReal ε := by
    exact (tendsto_order.1 htend).2 _ (by simpa using hε)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨K, fun k hk C _ => ?_⟩
  refine (coupling_abs_le P X Z N hN k C).trans ?_
  have := hK k hk
  have h2 : (P {ω | k < N ω}).toReal ≤ (ENNReal.ofReal ε).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top this.le
  rwa [ENNReal.toReal_ofReal hε.le] at h2

end PalmQueueing.Loynes

open PalmQueueing.Loynes
open MeasureTheory Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Ω) (X Z : ℕ → Ω → E)
    (hXmeas : ∀ n, Measurable (X n)) (hZmeas : ∀ n, Measurable (Z n))
    (hZcomp : IsShiftCompatible θ Z)
    (hcouple : Couple P X Z) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ C : Set (ℕ → E), MeasurableSet C →
        |(P {ω | (fun n : ℕ => X (n + k) ω) ∈ C}).toReal
          - (P {ω | (fun n : ℕ => Z (n + k) ω) ∈ C}).toReal| ≤ ε := by
  exact coupling_convergence_core P θ X Z hXmeas hZmeas hZcomp hcouple
