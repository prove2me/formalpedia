-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_triple__e3195b73385c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.711904+00:00
-- url     : https://prove2.me/submissions/b9380e6e-29b9-4acb-9604-cc19da6c89f2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = δ)
    (h2 : B * C + C * B = 0) : A * B * C - C * (A * B) = -(δ * B) := by
  calc A * B * C - C * (A * B) = A * (B * C + C * B) - (C * A + A * C) * B := by noncomm_ring
    _ = -(δ * B) := by rw [h1, h2]; noncomm_ring
end ReciprocityTheory.ChartRestriction.DS
