-- Prove2me | solution 1 for RobustMDP.Discounted.maxmin_value
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:16:27.329246+00:00
-- url     : https://prove2.me/submissions/074e5934-e2e4-406f-81b4-a84dcd55c240

import Theorems.Thm_RobustMDP_Discounted_robust_bellman_recursion
open RobustMDP.Discounted

theorem solution {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) (i₀ : Fin n) :
    ∃ v : Fin n → ℝ,
      M.bellmanOp v = v ∧ (∀ w, M.bellmanOp w = w → w = v) ∧
      IsLUB (Set.range fun P : M.StationaryNature =>
          ⨅ π : StationaryPolicy n A, M.discountedCost i₀ π P) (v i₀) := by
  obtain ⟨v,hv⟩ := robust_bellman_recursion M i₀
  exact ⟨v,hv.1.1,hv.1.2,hv.2.2.1.2⟩
