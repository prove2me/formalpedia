-- Prove2me | solution 1 for OnlinePrimalDual.MTS.standard_to_new
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:31:33.594235+00:00
-- url     : https://prove2.me/submissions/07d71406-f26a-4b3c-b132-bd461880e45a

import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar_d
import Definitions.Def_OnlinePrimalDual_MTS_costStandard

namespace OnlinePrimalDual.MTS

theorem aux_s2n_d_nonneg {V : Type*} (ws : WeightedStar V) (v : V) : 0 ≤ ws.d v := by
  unfold WeightedStar.d
  have := ws.hcenterDist_nonneg v
  linarith

end OnlinePrimalDual.MTS

open OnlinePrimalDual.MTS

theorem solution {V : Type*} {k : ℕ} (hk : 0 < k) (ws : WeightedStar V)
    (s : Fin k → V) (w : Fin k → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) :
    ∃ w' : Fin k → ℝ, ws.d (s ⟨0, hk⟩) ≤ w' ⟨0, hk⟩ ∧
      (∀ i, w' i ≤ w i + 2 * ws.d (s i)) ∧
      ∑ i, w' i ≤ 2 * costStandard ws s w := by
  refine ⟨fun i => w i + 2 * ws.d (s i), ?_, fun i => le_refl _, ?_⟩
  · have h1 := aux_s2n_d_nonneg ws (s ⟨0, hk⟩)
    have h2 := hw_nonneg ⟨0, hk⟩
    show ws.d (s ⟨0, hk⟩) ≤ w ⟨0, hk⟩ + 2 * ws.d (s ⟨0, hk⟩)
    linarith
  · unfold costStandard
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have := hw_nonneg i
    linarith
