-- Prove2me | solution 1 for StatComplexityDM.E2D.confidence_sets_contain_truth
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:36:46.451999+00:00
-- url     : https://prove2.me/submissions/a3336f9f-51a1-460f-9e0a-45fc7025113f

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_FoundationsRL_GeneralDM_LocalizedSubclass
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_E2D_Run

open StatComplexityDM.E2D
open FoundationsRL.GeneralDM

theorem solution {S Y : Type*} [Fintype S] [Fintype Y]
    (rew : Y → ℝ) (𝓜 : Set (S → Y → ℝ)) (piStar : (S → Y → ℝ) → S)
    (Mstar : S → Y → ℝ) (hMstar : Mstar ∈ 𝓜) (γ : ℝ) (T : ℕ) (R2 : ℝ)
    (Mhat : Fin T → S → Y → ℝ) (p : Fin T → S → ℝ) (Mt : Fin T → Set (S → Y → ℝ))
    (hrun : IsOptionIIRun 𝓜 rew piStar γ R2 T Mhat p Mt)
    (hE : EventD1 Mstar Mhat p Mt R2) :
    (∀ t : Fin T, Mstar ∈ Mt t) ∧
      ∑ t : Fin T, ∑ π, p t π * hellingerSq (Mstar π) (Mhat t π) ≤ R2 := by
  have hg : ∀ i : Fin T, 0 ≤ ∑ π, p i π * hellingerSq (Mstar π) (Mhat i π) := by
    intro i
    refine Finset.sum_nonneg (fun π _ => mul_nonneg ((hrun.2.1 i).1 π) ?_)
    exact Finset.sum_nonneg (fun y _ => sq_nonneg _)
  unfold EventD1 at hE
  have hsub : ∀ s : Finset (Fin T), (∀ i ∈ s, Mstar ∈ Mt i) →
      ∑ i ∈ s, ∑ π, p i π * hellingerSq (Mstar π) (Mhat i π) ≤ R2 := by
    intro s hs
    refine le_trans (le_of_eq ?_) (le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ s) ?_) hE)
    · exact Finset.sum_congr rfl (fun i hi => (if_pos (hs i hi)).symm)
    · intro i _ _
      split_ifs
      · exact hg i
      · exact le_rfl
  have main : ∀ n : ℕ, ∀ t : Fin T, (t : ℕ) = n → Mstar ∈ Mt t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht
      rw [hrun.1 t]
      refine ⟨?_, ?_⟩
      · split_ifs with h0
        · exact hMstar
        · exact ih ((t : ℕ) - 1) (by omega) _ rfl
      · apply hsub
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact ih i (by rw [← ht]; exact hi) i rfl
  have h1 : ∀ t : Fin T, Mstar ∈ Mt t := fun t => main t t rfl
  exact ⟨h1, hsub Finset.univ (fun i _ => h1 i)⟩
