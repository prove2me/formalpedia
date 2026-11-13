-- Prove2me | solution 1 for TeschlQM.Atomic.hvz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T10:56:59.68283+00:00
-- url     : https://prove2.me/submissions/0d9ab8bf-bc28-448e-857d-64e7cd412285

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian
import Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_isBoundedBelow
import Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_exists_min_spectrum
import Theorems.Thm_TeschlQM_Atomic_essentialSpectrum_atomicHamiltonian_eq_Ici
import Theorems.Thm_TeschlQM_Atomic_hydrogen_groundState_mem_spectrum

/-! Reduction of Teschl Theorem 11.2 (HVZ) to four children:
semiboundedness (Thm 11.1), existence of min σ(H^(M)), the essential-spectrum identity (11.9),
and the hydrogen ground-state energy -γ²/4 ∈ σ(H^(1)). Negativity of λ^{N-1} for N ≥ 2 follows by
induction: λ^{M-1} ∈ σ_ess(H^(M)) ⊆ σ(H^(M)) gives λ^M ≤ λ^{M-1}, and λ^1 ≤ -γ²/4 < 0. -/

open TeschlQM.Atomic in
theorem solution (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ) (hN : 1 ≤ N) :
    (∃ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee N) γ) ∧
      ∃ lam : ℝ, ((lam : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)) ∧
          ∀ z ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)), z.im = 0 ∧ lam ≤ z.re) ∧
        (2 ≤ N → lam < 0) ∧
        TeschlQM.Shared.essentialSpectrum (atomicHamiltonian γne γee N) =
          (fun t : ℝ => (t : ℂ)) '' Set.Ici lam := by
  refine ⟨TeschlQM.Atomic.atomicHamiltonian_isBoundedBelow γne γee hne hee N, ?_⟩
  obtain ⟨lam, hmem, hmin⟩ :=
    TeschlQM.Atomic.atomicHamiltonian_exists_min_spectrum γne γee hne hee (N - 1)
  refine ⟨lam, ⟨hmem, hmin⟩, ?_,
    TeschlQM.Atomic.essentialSpectrum_atomicHamiltonian_eq_Ici γne γee hne hee N hN lam hmem hmin⟩
  intro h2N
  have key : ∀ M : ℕ, ∀ l : ℝ,
      (l : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (M + 1)) →
      (∀ z ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (M + 1)), z.im = 0 ∧ l ≤ z.re) →
      l ≤ -(γne ^ 2 / 4) := by
    intro M
    induction M with
    | zero =>
      intro l _ hm
      have := (hm _ (TeschlQM.Atomic.hydrogen_groundState_mem_spectrum γne γee hne hee)).2
      rw [Complex.ofReal_re] at this
      exact this
    | succ M ih =>
      intro l _ hm
      obtain ⟨l', hl', hm'⟩ :=
        TeschlQM.Atomic.atomicHamiltonian_exists_min_spectrum γne γee hne hee (M + 1)
      have hess := TeschlQM.Atomic.essentialSpectrum_atomicHamiltonian_eq_Ici γne γee hne hee
        (M + 1 + 1) (by omega) l' hl' hm'
      have hin : ((l' : ℝ) : ℂ) ∈
          TeschlQM.Shared.essentialSpectrum (atomicHamiltonian γne γee (M + 1 + 1)) := by
        rw [hess]; exact ⟨l', Set.mem_Ici.2 le_rfl, rfl⟩
      have h1' := (hm _ hin.1).2
      have h2' := ih l' hl' hm'
      simp only [Complex.ofReal_re] at h1'
      linarith
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 2 := ⟨N - 2, by omega⟩
  have := key K lam hmem hmin
  have : 0 < γne ^ 2 / 4 := by positivity
  linarith
