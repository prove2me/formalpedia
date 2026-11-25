-- Prove2me | solution 1 for PI.AprimeInfG.continuous_embed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:03.717164+00:00
-- url     : https://prove2.me/submissions/7a2db170-d47e-43d4-8c96-aa2b144962c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_BlockEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open scoped Matrix
variable {n k : ℕ} {S : Finset (Fin n)}
namespace PI.AprimeInfG
theorem _root_.solution (e : Fin k ≃ S) : Continuous (emb0 e) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i ∈ S ∧ j ∈ S
  · simp only [emb0, dif_pos h]
    exact continuous_id.matrix_elem _ _
  · simp only [emb0, dif_neg h]
    exact continuous_const
end PI.AprimeInfG
