-- Prove2me | solution 1 for R03SP08NativeBridgeless.neighbor_ncard_of_cubic
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:15.711412+00:00
-- url     : https://prove2.me/submissions/34ddc57f-3f09-4e6d-84c0-e6de8128cb78

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_117d348ee0_SP08_NATIVE_BRIDGELESS_FROM_3CONN_CUBIC_v1

/-!
Candidate-only native graph lemma.  It derives absence of native graph
bridges from the exact frozen ThreeVertexConnected and Cubic predicates.  It
is deliberately independent of planarity, rotation systems, source
hypermaps, and the Four-Colour theorem.
-/

namespace R03SP08NativeBridgeless

open CubicP3Partition

universe u
variable {V : Type u} [Fintype V]

end R03SP08NativeBridgeless

open R03SP08NativeBridgeless
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution {G : SimpleGraph V}
    (hcubic : Cubic G) (u : V) : (G.neighborSet u).ncard = 3 := by
  have hu := hcubic u
  change Nat.card {w : V // G.Adj u w} = 3 at hu
  change (G.neighborSet u).ncard = 3
  change Nat.card (G.neighborSet u) = 3
  rw [Nat.card_coe_set_eq]
  exact hu
