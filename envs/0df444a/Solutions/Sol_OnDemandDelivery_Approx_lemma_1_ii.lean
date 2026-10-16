-- Prove2me | solution 1 for OnDemandDelivery.Approx.lemma_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:00:50.864296+00:00
-- url     : https://prove2.me/submissions/ca8b479f-03c4-4ae3-bd6f-ff31fd1e7735

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal
open OnDemandDelivery.Approx

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Sheng Liu and Zhixing Luo, arXiv:2107.13058v3, Lemma 1(ii).
theorem solution {L : Type*} [Fintype L] (M : Model L) (_hM : M.Standing) (n : ℕ)
    (_hn : 1 ≤ n) (_hnN : n ≤ M.N) (ω : ℕ → ℕ → ℕ → ℝ≥0)
    (ζ₁ ζ₂ : ℕ → ℕ) (h : ζ₂ ≤ ζ₁) : M.Vapt n ζ₂ ω ≤ M.Vapt n ζ₁ ω := by
  unfold Model.Vapt
  refine le_iInf₂ fun K hK => ?_
  have hK₂ : M.AptFeasible n ζ₂ ω K := by
    intro j hj
    exact (hK j hj).trans (sub_le_sub_left (by exact_mod_cast h j) _)
  exact iInf₂_le_of_le K hK₂ le_rfl

#print axioms solution
