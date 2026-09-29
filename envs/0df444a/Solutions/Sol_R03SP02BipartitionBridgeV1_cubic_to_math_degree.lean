-- Prove2me | solution 1 for R03SP02BipartitionBridgeV1.cubic_to_math_degree
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:47.977579+00:00
-- url     : https://prove2.me/submissions/d1015655-04b6-4adf-b283-bce2230bffbd

import Definitions.Def_cubic_p3_partition_models

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace R03SP02BipartitionBridgeV1

open CubicP3Partition
open scoped BigOperators

noncomputable section

variable {V : Type} [Fintype V]


end
end R03SP02BipartitionBridgeV1

open R03SP02BipartitionBridgeV1
open CubicP3Partition
open scoped BigOperators
variable {V : Type} [Fintype V]
theorem solution (G : SimpleGraph V) (hC : Cubic G)
    [DecidableRel G.Adj] : ∀ v, G.degree v = 3 := by
  intro v
  have hv := hC v
  unfold CubicP3Partition.degree at hv
  rw [Nat.card_eq_fintype_card] at hv
  change Finset.card (G.neighborFinset v) = 3
  rw [SimpleGraph.neighborFinset_def, Set.toFinset_card]
  exact hv

