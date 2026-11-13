-- Prove2me | solution 1 for TeschlQM.Atomic.atomicHamiltonian_localization_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T08:26:15.567199+00:00
-- url     : https://prove2.me/submissions/70b516ea-7756-4a45-9251-8c15f129a784

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian
import Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_localization_lower_bound_schwartz
import Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_form_lower_bound_of_schwartz

/-! Reduction of the IMS localization lower bound (D3c of 7ab9d8bf) to two children: the bound on the
Schwartz core (IMS localization) and its extension to the operator domain of H^N. -/

set_option autoImplicit false

open TeschlQM.Atomic MeasureTheory Filter in
theorem solution (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee)
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ)
    (hlam : TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee (N - 1)) lam) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ, Measurable W ∧ (∃ C : ℝ, ∀ x, |W x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε) ∧
      ∀ (ψ : (freeHamiltonian (Fin N × Fin 3)).domain)
        (hψ : (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈ (atomicHamiltonian γne γee N).domain),
        (lam - δ) * ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ^ 2
          - δ * (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (freeHamiltonian (Fin N × Fin 3) ψ)).re
          - ∫ x, W x * ‖((ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) : EuclideanSpace ℝ (Fin N × Fin 3) → ℂ) x‖ ^ 2
          ≤ (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (atomicHamiltonian γne γee N ⟨ψ, hψ⟩)).re := by
  obtain ⟨W, hWm, ⟨C, hWC⟩, hdec, hX⟩ :=
    TeschlQM.Atomic.atomicHamiltonian_localization_lower_bound_schwartz γne γee hne hee N hN lam hlam δ hδ
  refine ⟨W, hWm, ⟨C, hWC⟩, hdec, fun ψ hψ => ?_⟩
  have key := TeschlQM.Atomic.atomicHamiltonian_form_lower_bound_of_schwartz γne γee N lam δ W hWm C hWC hX ψ hψ
  have hpos : 0 ≤ δ * ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ^ 2 := by
    positivity
  nlinarith
