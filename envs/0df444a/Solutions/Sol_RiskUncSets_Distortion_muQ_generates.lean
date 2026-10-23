-- Prove2me | solution 1 for RiskUncSets.Distortion.muQ_generates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:00:40.819503+00:00
-- url     : https://prove2.me/submissions/86b142ab-6c82-4860-9347-ffc46890292b

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

open RiskUncSets.Distortion Finset MeasureTheory



/-- rearrangement: antitone weights, sorted (monotone) arrangement is maximal for `∑ q_i (-X_i)`. -/
theorem ru83_rearr {N : ℕ} (q X : Fin N → ℝ) (hq : Antitone q) (π σ : Equiv.Perm (Fin N))
    (hπ : Monotone (X ∘ π)) :
    ∑ i, q i * (-X (σ i)) ≤ ∑ i, q i * (-X (π i)) := by
  have hg : Antitone (fun i => -X (π i)) := fun a b hab => by
    have := hπ hab; simp only [Function.comp] at this; linarith
  have hmv : Monovary q (fun i => -X (π i)) := hq.monovary hg
  have := hmv.sum_mul_comp_perm_le_sum_mul (σ := σ.trans π.symm)
  simpa using this

theorem ru83_reindex {N : ℕ} (f h : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ∑ i, f (σ i) * h i = ∑ j, f j * h (σ.symm j) := by
  rw [← Equiv.sum_comp σ.symm]; simp

theorem ru83_muQ_generates {N : ℕ} (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N) :
    Generates (Set.range fun σ : Equiv.Perm (Fin N) => q ∘ σ) (muQ q) := by
  obtain ⟨⟨hq0, hq1⟩, hqa⟩ := hq
  refine ⟨?_, fun X => ?_⟩
  · rintro _ ⟨σ, rfl⟩
    refine ⟨fun i => hq0 _, ?_⟩
    simp only [Function.comp]
    rw [Equiv.sum_comp σ q, hq1]
  · have hτ : Monotone (X ∘ Tuple.sort X) := Tuple.monotone_sort X
    have hS : muQ q X = ∑ i, q i * (-X (Tuple.sort X i)) := by
      simp [muQ, mul_neg, sum_neg_distrib]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      simp only [Function.comp]
      rw [ru83_reindex q (fun i => -X i) σ, hS]
      exact ru83_rearr q X hqa _ _ hτ
    · intro b hb
      apply hb
      refine ⟨q ∘ (Tuple.sort X).symm, ⟨(Tuple.sort X).symm, rfl⟩, ?_⟩
      simp only [Function.comp]
      rw [ru83_reindex q (fun i => -X i) (Tuple.sort X).symm, hS]
      simp


theorem solution {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N) :
    Generates (Set.range fun σ : Equiv.Perm (Fin N) => q ∘ σ) (muQ q) := by


  exact ru83_muQ_generates q hq
