-- Prove2me | solution 1 for TwoAgentSched.reduction
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T13:28:22.89047+00:00
-- url     : https://prove2.me/submissions/66304f27-cd83-4845-8fb2-fdd8d0a002bd

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_fAmax
import Definitions.Def_TwoAgentSched_fComb

open TwoAgentSched

namespace TwoAgentSched.ReductionProof

variable {nA nB : ℕ}

lemma combMax_le_fAmax_of_BOk (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (C : Job nA nB → ℝ) (hB : BOk fB Q C) :
    combMax fA fB Q C ≤ fAmax fA C := by
  rw [combMax, Finset.sup_le_iff]
  intro j _
  cases j with
  | inl h =>
      simpa [fAmax, fComb] using
        (Finset.le_sup (s := Finset.univ)
          (f := fun h => ((fA h (C (Sum.inl h)) : ℝ) : EReal)) (Finset.mem_univ h))
  | inr k =>
      have hk : ¬ Q < fB k (C (Sum.inr k)) := not_lt.mpr (hB k)
      simp [fComb, hk]

lemma fAmax_le_combMax (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (C : Job nA nB → ℝ) :
    fAmax fA C ≤ combMax fA fB Q C := by
  rw [fAmax, Finset.sup_le_iff]
  intro h _
  rw [combMax]
  exact Finset.le_sup (s := Finset.univ)
    (f := fun j => fComb fA fB Q j (C j)) (Finset.mem_univ (Sum.inl h))

lemma combMax_eq_fAmax_of_BOk (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (C : Job nA nB → ℝ) (hB : BOk fB Q C) :
    combMax fA fB Q C = fAmax fA C :=
  le_antisymm (combMax_le_fAmax_of_BOk fA fB Q C hB) (fAmax_le_combMax fA fB Q C)

lemma fAmax_lt_top (fA : Fin nA → ℝ → ℝ) (C : Job nA nB → ℝ) :
    fAmax fA C < ⊤ := by
  rw [fAmax, Finset.sup_lt_iff (show (⊥ : EReal) < ⊤ by simp)]
  intro h _
  exact EReal.coe_lt_top _

lemma combMax_lt_top_imp_BOk (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (C : Job nA nB → ℝ) (hlt : combMax fA fB Q C < ⊤) :
    BOk fB Q C := by
  intro k
  have hlt' : fComb fA fB Q (Sum.inr k) (C (Sum.inr k)) < ⊤ := by
    rw [combMax, Finset.sup_lt_iff (show (⊥ : EReal) < ⊤ by simp)] at hlt
    exact hlt (Sum.inr k) (Finset.mem_univ _)
  by_contra hk
  have hQ : Q < fB k (C (Sum.inr k)) := lt_of_not_ge hk
  have htop : (⊤ : EReal) < ⊤ := by simpa [fComb, hQ] using hlt'
  exact (lt_irrefl (⊤ : EReal)) htop

end TwoAgentSched.ReductionProof

open TwoAgentSched
open TwoAgentSched.ReductionProof

theorem solution {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (Q : ℝ) (_hp : ∀ j, 0 ≤ p j) (_hfA : ∀ h, MonotoneOn (fA h) (Set.Ici 0))
    (_hfB : ∀ k, MonotoneOn (fB k) (Set.Ici 0))
    (Sstar : Job nA nB → ℝ) (_hSstar : Feasible p Sstar)
    (hopt : ∀ S, Feasible p S →
      combMax fA fB Q (fun j => Sstar j + p j) ≤ combMax fA fB Q (fun j => S j + p j)) :
    (combMax fA fB Q (fun j => Sstar j + p j) < ⊤ →
      BOk fB Q (fun j => Sstar j + p j) ∧
      (∀ S, Feasible p S → BOk fB Q (fun j => S j + p j) →
        fAmax fA (fun j => Sstar j + p j) ≤ fAmax fA (fun j => S j + p j)) ∧
      fAmax fA (fun j => Sstar j + p j) = combMax fA fB Q (fun j => Sstar j + p j)) ∧
    (combMax fA fB Q (fun j => Sstar j + p j) = ⊤ →
      ¬ ∃ S, Feasible p S ∧ BOk fB Q (fun j => S j + p j)) := by
  constructor
  · intro hlt
    have hB : BOk fB Q (fun j => Sstar j + p j) :=
      combMax_lt_top_imp_BOk fA fB Q _ hlt
    have hEq : combMax fA fB Q (fun j => Sstar j + p j) =
        fAmax fA (fun j => Sstar j + p j) :=
      combMax_eq_fAmax_of_BOk fA fB Q _ hB
    refine ⟨hB, ?_, hEq.symm⟩
    intro S hS hBS
    have hEqS : combMax fA fB Q (fun j => S j + p j) =
        fAmax fA (fun j => S j + p j) :=
      combMax_eq_fAmax_of_BOk fA fB Q _ hBS
    have hoptS := hopt S hS
    rw [hEq, hEqS] at hoptS
    exact hoptS
  · intro htop hfeas
    obtain ⟨S, hS, hBS⟩ := hfeas
    have hEqS : combMax fA fB Q (fun j => S j + p j) =
        fAmax fA (fun j => S j + p j) :=
      combMax_eq_fAmax_of_BOk fA fB Q _ hBS
    have hltS : combMax fA fB Q (fun j => S j + p j) < ⊤ := by
      rw [hEqS]
      exact fAmax_lt_top fA _
    have hoptS := hopt S hS
    rw [htop] at hoptS
    exact (not_le_of_gt hltS) hoptS
