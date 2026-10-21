-- Prove2me | solution 1 for TwoAgentSched.MaxMax.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:37:13.507377+00:00
-- url     : https://prove2.me/submissions/e1300187-a495-4e31-9a7c-d81582561600

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_Model

set_option autoImplicit false
open TwoAgentSched.MaxMax

theorem solution {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : Job nA nB → ℝ)
    (hp : ∀ j, 0 ≤ p j) (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σstar σtilde : List (Job nA nB)) (hstar : IsOptimal hA p fA fB Q σstar)
    (htilde : IsOptimalSwap hB p fA fB (maxCostA hA p fA σstar) σtilde) :
    IsNondominated hA hB p fA fB σtilde := by
  obtain ⟨⟨hsched, hfeA⟩, hopt⟩ := htilde
  have hAle : maxCostA hA p fA σtilde ≤ maxCostA hA p fA σstar :=
    Finset.sup'_le _ _ (fun h _ => hfeA h)
  have hstarB : maxCostB hB p fB σstar ≤ Q :=
    Finset.sup'_le _ _ (fun k _ => hstar.1.2 k)
  have hstar_swap : IsFeasibleSwap p fA (maxCostA hA p fA σstar) σstar :=
    ⟨hstar.1.1, fun h => Finset.le_sup'
      (fun h => fA h (MooreLateJobs.Shared.completionTime p σstar (Sum.inl h)))
      (Finset.mem_univ h)⟩
  have hBtilde : maxCostB hB p fB σtilde ≤ Q := (hopt σstar hstar_swap).trans hstarB
  refine ⟨hsched, ?_⟩
  rintro ⟨l', hl', h1, h2, h3⟩
  have hl'swap : IsFeasibleSwap p fA (maxCostA hA p fA σstar) l' :=
    ⟨hl', fun h => (Finset.le_sup'
      (fun h => fA h (MooreLateJobs.Shared.completionTime p l' (Sum.inl h)))
      (Finset.mem_univ h)).trans (h1.trans hAle)⟩
  have hBl' := hopt l' hl'swap
  rcases h3 with h3 | h3
  · have hl'feas : IsFeasible p fB Q l' :=
      ⟨hl', fun k => (Finset.le_sup'
        (fun k => fB k (MooreLateJobs.Shared.completionTime p l' (Sum.inr k)))
        (Finset.mem_univ k)).trans (h2.trans hBtilde)⟩
    have := hstar.2 l' hl'feas
    linarith
  · linarith
