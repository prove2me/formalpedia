-- Prove2me | solution 1 for TwoAgentSched.MaxMax.reduction_to_fmax
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:36:37.856087+00:00
-- url     : https://prove2.me/submissions/5f33df95-1013-457a-bd29-f14dba50b6b3

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_Reduction

set_option autoImplicit false
open TwoAgentSched.MaxMax

lemma tas_reducedMax_eq {nA nB : ℕ} (hA : 0 < nA) (p : Job nA nB → ℝ)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (l : List (Job nA nB))
    (hl : ∀ k : Fin nB, fB k (MooreLateJobs.Shared.completionTime p l (Sum.inr k)) ≤ Q) :
    reducedMax p fA fB Q l = (maxCostA hA p fA l : EReal) := by
  apply le_antisymm
  · unfold reducedMax
    apply Finset.sup_le
    rintro (h | k) _
    · simp only [reducedCost]
      exact_mod_cast Finset.le_sup'
        (fun h => fA h (MooreLateJobs.Shared.completionTime p l (Sum.inl h))) (Finset.mem_univ h)
    · simp [reducedCost, hl k]
  · obtain ⟨h, _, hh⟩ := Finset.exists_mem_eq_sup'
      (⟨⟨0, hA⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin nA)).Nonempty)
      (fun h => fA h (MooreLateJobs.Shared.completionTime p l (Sum.inl h)))
    unfold maxCostA
    rw [hh]
    exact Finset.le_sup (f := fun j => reducedCost fA fB Q j (MooreLateJobs.Shared.completionTime p l j))
      (Finset.mem_univ (Sum.inl h))

theorem solution {nA nB : ℕ} (hA : 0 < nA) (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (hfA : ∀ h, Monotone (fA h))
    (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) (σ : List (Job nA nB))
    (hσ : MooreLateJobs.Shared.IsSchedule Finset.univ σ)
    (hmin : ∀ σ' : List (Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ σ' →
      reducedMax p fA fB Q σ ≤ reducedMax p fA fB Q σ') :
    (∀ fstar : ℝ, reducedMax p fA fB Q σ = (fstar : EReal) →
      IsOptimal hA p fA fB Q σ ∧ maxCostA hA p fA σ = fstar) ∧
    (reducedMax p fA fB Q σ = ⊤ → ¬ ∃ l : List (Job nA nB), IsFeasible p fB Q l) := by
  constructor
  · intro fstar hfs
    have hfeas : ∀ k : Fin nB, fB k (MooreLateJobs.Shared.completionTime p σ (Sum.inr k)) ≤ Q := by
      intro k
      by_contra hk
      have h0 : reducedCost fA fB Q (Sum.inr k)
          (MooreLateJobs.Shared.completionTime p σ (Sum.inr k)) = ⊤ := by
        simp [reducedCost, hk]
      have h1 : (⊤ : EReal) ≤ reducedMax p fA fB Q σ := by
        rw [← h0]
        exact Finset.le_sup (f := fun j => reducedCost fA fB Q j
          (MooreLateJobs.Shared.completionTime p σ j)) (Finset.mem_univ _)
      rw [hfs] at h1
      exact absurd h1 (not_le.mpr (EReal.coe_lt_top fstar))
    have hE := tas_reducedMax_eq hA p fA fB Q σ hfeas
    rw [hfs] at hE
    have hEq : maxCostA hA p fA σ = fstar := by exact_mod_cast hE.symm
    refine ⟨⟨⟨hσ, hfeas⟩, ?_⟩, hEq⟩
    intro l' hl'
    have h2 := hmin l' hl'.1
    rw [tas_reducedMax_eq hA p fA fB Q σ hfeas, tas_reducedMax_eq hA p fA fB Q l' hl'.2] at h2
    exact_mod_cast h2
  · rintro htop ⟨l, hl⟩
    have h2 := hmin l hl.1
    rw [htop, tas_reducedMax_eq hA p fA fB Q l hl.2] at h2
    exact absurd h2 (not_le.mpr (EReal.coe_lt_top _))
