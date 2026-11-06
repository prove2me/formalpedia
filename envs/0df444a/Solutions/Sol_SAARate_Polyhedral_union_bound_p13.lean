-- Prove2me | solution 1 for SAARate.Polyhedral.union_bound_p13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:57:16.944688+00:00
-- url     : https://prove2.me/submissions/9f08286e-1b8d-40d1-903b-94e0984057a6

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting

open MeasureTheory ProbabilityTheory

open SAARate.Polyhedral in
theorem solution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : SAARate.Sharp.E m → Ω → ℝ) (Θ : Set (SAARate.Sharp.E m))
    {S : Type*} [MeasurableSpace S] (Q : Measure S) (ω : ℕ → S → Ω)
    (q ℓ : ℕ) (x : Fin q → SAARate.Sharp.E m)
    (hc : ∀ (s : ℕ → Ω) (N : ℕ),
      (∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val → SAARate.Sharp.saaObj h s N (x i) < SAARate.Sharp.saaObj h s N (x j)) →
        (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ))
    (hgap : ∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val →
      SAARate.Sharp.expectedObj P h (x i) < SAARate.Sharp.expectedObj P h (x j)) :
    ∃ ε > 0, ∀ N : ℕ,
      Q {s | ¬ ((SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun k => ω k s) N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun k => ω k s) N) Θ))} ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < ℓ),
            Q {s | SAARate.Sharp.expectedObj P h (x i) + ε ≤ SAARate.Sharp.saaObj h (fun k => ω k s) N (x i)}) +
          ∑ j ∈ Finset.univ.filter (fun j : Fin q => ℓ ≤ j.val),
            Q {s | SAARate.Sharp.saaObj h (fun k => ω k s) N (x j) ≤ SAARate.Sharp.expectedObj P h (x j) - ε} := by
  set f := SAARate.Sharp.expectedObj P h
  -- a uniform positive lower bound `2ε` on the gaps
  obtain ⟨ε, hε, hεgap⟩ : ∃ ε > 0, ∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val →
      2 * ε ≤ f (x j) - f (x i) := by
    classical
    let T := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1.val < ℓ ∧ ℓ ≤ p.2.val)
    by_cases hT : T.Nonempty
    · refine ⟨(T.inf' hT (fun p => f (x p.2) - f (x p.1))) / 2, ?_, ?_⟩
      · have : 0 < T.inf' hT (fun p => f (x p.2) - f (x p.1)) := by
          rw [Finset.lt_inf'_iff]
          intro p hp
          simp only [T, Finset.mem_filter] at hp
          linarith [hgap p.1 p.2 hp.2.1 hp.2.2]
        linarith
      · intro i j hi hj
        have : T.inf' hT (fun p => f (x p.2) - f (x p.1)) ≤ f (x j) - f (x i) :=
          Finset.inf'_le (f := fun p : Fin q × Fin q => f (x p.2) - f (x p.1))
            (show (i, j) ∈ T from Finset.mem_filter.2 ⟨Finset.mem_univ _, hi, hj⟩)
        linarith
    · refine ⟨1, one_pos, ?_⟩
      intro i j hi hj
      exact absurd ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hi, hj⟩⟩ hT
  refine ⟨ε, hε, fun N => ?_⟩
  set A := fun i : Fin q => {s | f (x i) + ε ≤ SAARate.Sharp.saaObj h (fun k => ω k s) N (x i)}
  set B := fun j : Fin q => {s | SAARate.Sharp.saaObj h (fun k => ω k s) N (x j) ≤ f (x j) - ε}
  have hsub : {s | ¬ ((SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun k => ω k s) N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn f Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun k => ω k s) N) Θ))} ⊆
      (⋃ i ∈ Finset.univ.filter (fun i : Fin q => i.val < ℓ), A i) ∪
        (⋃ j ∈ Finset.univ.filter (fun j : Fin q => ℓ ≤ j.val), B j) := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs
    have hn : ¬ ∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val →
        SAARate.Sharp.saaObj h (fun k => ω k s) N (x i) < SAARate.Sharp.saaObj h (fun k => ω k s) N (x j) :=
      fun H => hs (hc _ N H)
    push Not at hn
    obtain ⟨i, j, hi, hj, hle⟩ := hn
    have g2 := hεgap i j hi hj
    by_cases hA : f (x i) + ε ≤ SAARate.Sharp.saaObj h (fun k => ω k s) N (x i)
    · left
      simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hi, hA⟩
    · right
      simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨j, hj, ?_⟩
      show SAARate.Sharp.saaObj h (fun k => ω k s) N (x j) ≤ f (x j) - ε
      push Not at hA
      linarith
  calc _ ≤ Q ((⋃ i ∈ Finset.univ.filter (fun i : Fin q => i.val < ℓ), A i) ∪
        (⋃ j ∈ Finset.univ.filter (fun j : Fin q => ℓ ≤ j.val), B j)) := measure_mono hsub
    _ ≤ Q (⋃ i ∈ Finset.univ.filter (fun i : Fin q => i.val < ℓ), A i) +
        Q (⋃ j ∈ Finset.univ.filter (fun j : Fin q => ℓ ≤ j.val), B j) := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)
