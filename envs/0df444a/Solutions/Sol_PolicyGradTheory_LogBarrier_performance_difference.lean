-- Prove2me | solution 1 for PolicyGradTheory.LogBarrier.performance_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:58:43.874657+00:00
-- url     : https://prove2.me/submissions/f0ce5584-53f5-42a7-94de-7f249675ccc8

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Theorems.Thm_PolicyGradTheory_NPG_performance_difference

open FoundationsML.ReinforcementLearning

/-- Lemma 3.2 (the performance difference lemma), arXiv:1908.00261v5, p. 12:
`V^π(s₀) − V^{π'}(s₀) = (1/(1−γ)) E_{s∼d^π_{s₀}} E_{a∼π(·|s)} [A^{π'}(s,a)]`,
where `d^π_{s₀}` is the discounted state PolicyGradTheory.ProjGA.visitation (4) started from the point mass at `s₀`. -/
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s₀ : S) :
    PolicyValue π P r γ s₀ - PolicyValue π' P r γ s₀ =
      1 / (1 - γ) * ∑ s, PolicyGradTheory.ProjGA.visitation π P γ (fun s' => if s' = s₀ then 1 else 0) s *
        ∑ a, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a := by
  apply PolicyGradTheory.NPG.performance_difference <;> assumption


