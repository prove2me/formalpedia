-- Prove2me | solution 1 for TwoAgentSched.ParetoMax.lemma_11_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:24:07.405175+00:00
-- url     : https://prove2.me/submissions/6c21d6ad-fe9b-4b2f-9321-4c518d30687c

import Definitions.Def_TwoAgentSched_ParetoMax_Model
import Theorems.Thm_TwoAgentSched_ParetoMax_lemma_11_2

set_option autoImplicit false
open TwoAgentSched.ParetoMax

theorem solution {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k))
    (yA yB yA' yB' : ℝ)
    (hy : IsNondominatedPair hA hB p fA fB (yA, yB))
    (hy' : IsNondominatedPair hA hB p fA fB (yA', yB'))
    (hAlt : yA < yA') (hBgt : yB' < yB) (h : Fin nA) (k : Fin nB) :
    ∃ σ σ' : List (TwoAgentSched.MaxMax.Job nA nB),
      IsNondominatedFor hA hB p fA fB (yA, yB) σ ∧
      IsNondominatedFor hA hB p fA fB (yA', yB') σ' ∧
      (Precedes σ (Sum.inr k) (Sum.inl h) → Precedes σ' (Sum.inr k) (Sum.inl h)) := by
  obtain ⟨σ, σ', hσ, hσ', hall⟩ := lemma_11_2 hA hB p hp fA fB hfA hfB yA yB yA' yB' hy hy' hAlt hBgt
  exact ⟨σ, σ', hσ, hσ', hall h k⟩
