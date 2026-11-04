-- Prove2me | solution 1 for RobustMultitask.Estimator.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:14:23.223724+00:00
-- url     : https://prove2.me/submissions/6877890d-c6c0-42d5-aede-2b0224018080

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Theorems.Thm_RobustMultitask_Estimator_lemma_1
import Theorems.Thm_RobustMultitask_Estimator_eq_16_poor_component_error
import Theorems.Thm_RobustMultitask_Estimator_final_l1_bound

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal
open RobustMultitask.Estimator

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (ψ : ℝ) (hA1 : Assumption1 n X ψ)
    (C₀ ζ η : ℝ) (hC₀ : 2 < C₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 - 1 / C₀ - ζ)
    (j : Fin N) (lam : ℝ) (hlam : 0 < lam) (βhat : Ω → Fin d → ℝ)
    (hβhat : ∀ ω, IsRMEstimate n X (fun k => response X β ε k ω) (ζ + η) lam j (βhat ω)) :
    P {ω | 6 * lam * s / (ζ * ψ)
            + 4 * C₀ * d * (3 * ζ + 4 * η)
              * (⨆ i, Real.sqrt ((σ i : ℝ) ^ 2 / ((n i : ℝ) * ψ) * Real.log (3 / η)))
          < l1 (βhat ω - β j)}
      ≤ ENNReal.ofReal (3 * d * Real.exp (-((N : ℝ) * η ^ 2) / 9)
          + 2 * d * Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2))) := by
  have hψ : 0 < ψ := hA1.1
  have hN : 0 < N := Fin.pos j
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: the ℓ¹ norm vanishes and the threshold is nonnegative, so the event is empty.
    subst hd
    have hempty : {ω | 6 * lam * s / (ζ * ψ)
            + 4 * C₀ * ((0 : ℕ) : ℝ) * (3 * ζ + 4 * η)
              * (⨆ i, Real.sqrt ((σ i : ℝ) ^ 2 / ((n i : ℝ) * ψ) * Real.log (3 / η)))
          < l1 (βhat ω - β j)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h0 : l1 (βhat ω - β j) = 0 := by simp [l1]
      rw [h0]
      have : 0 ≤ 6 * lam * s / (ζ * ψ) := by positivity
      simpa using this
    rw [hempty, measure_empty]
    exact zero_le
  · -- the two bad events
    set M := ⨆ i, Real.sqrt ((σ i : ℝ) ^ 2 / ((n i : ℝ) * ψ) * Real.log (3 / η)) with hM
    let A : Set Ω := {ω | C₀ * d * (3 * ζ + 4 * η) * M
          ≤ l1 (restrict (poorlyAligned β βdag ζ)
              (sharedEst n X (ζ + η) (fun k => response X β ε k ω) - βdag))}
    let B : Set Ω := {ω | ¬ ((2 / (n j : ℝ)) * linf ((X j)ᵀ *ᵥ (fun k => ε j k ω)) ≤ lam / 2)}
    have hA : P A ≤ ENNReal.ofReal (3 * d * Real.exp (-((N : ℝ) * η ^ 2) / 9)) :=
      eq_16_poor_component_error P n X β βdag s σ ε hmodel hN hd ψ hA1 C₀ ζ η hC₀ hζ0 hζ1 hη0 hη1
    have hB : P B ≤ ENNReal.ofReal
          (2 * d * Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2))) :=
      lemma_1 P n X β βdag s σ ε hmodel j lam hlam
    have hsub : {ω | 6 * lam * s / (ζ * ψ) + 4 * C₀ * d * (3 * ζ + 4 * η) * M
          < l1 (βhat ω - β j)} ⊆ A ∪ B := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_contra hc
      simp only [Set.mem_union, A, B, Set.mem_ofPred_eq, not_or, not_le] at hc
      obtain ⟨hcA, hcB⟩ := hc
      have hfin := (final_l1_bound (X j) β βdag s ζ ψ j lam (fun k => ε j k ω)
        (sharedEst n X (ζ + η) (fun k => response X β ε k ω)) (βhat ω) (hmodel.pos_n j)
        hmodel.sparse hψ (hA1.2 j) hζ0 hζ1 hlam (not_lt.mp hcB) (hβhat ω)).2
      have : 6 * (s : ℝ) * lam / (ζ * ψ) = 6 * lam * s / (ζ * ψ) := by ring
      linarith
    calc P _ ≤ P (A ∪ B) := measure_mono hsub
      _ ≤ P A + P B := measure_union_le A B
      _ ≤ _ + _ := add_le_add hA hB
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
