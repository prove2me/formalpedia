-- Prove2me | solution 1 for R03SP08NativeBridgeless.exists_neighbor_ne_of_cubic
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:13.014052+00:00
-- url     : https://prove2.me/submissions/4e6a7301-915b-4de2-ba30-55811cc90753

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

lemma neighbor_ncard_of_cubic {G : SimpleGraph V}
    (hcubic : Cubic G) (u : V) : (G.neighborSet u).ncard = 3 := by
  have hu := hcubic u
  change Nat.card {w : V // G.Adj u w} = 3 at hu
  change (G.neighborSet u).ncard = 3
  change Nat.card (G.neighborSet u) = 3
  rw [Nat.card_coe_set_eq]
  exact hu


end R03SP08NativeBridgeless

open R03SP08NativeBridgeless
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution {G : SimpleGraph V}
    (hcubic : Cubic G) {u v : V} (huv : G.Adj u v) :
    ∃ w, G.Adj u w ∧ w ≠ v := by
  have hn : (G.neighborSet u).ncard = 3 := neighbor_ncard_of_cubic hcubic u
  have hv : v ∈ G.neighborSet u := (G.mem_neighborSet u v).2 huv
  have hlt : ({v} : Set V).ncard < (G.neighborSet u).ncard := by
    simp [hn]
  obtain ⟨w, hw, hwv⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({v} : Set V)) (t := G.neighborSet u) hlt
  exact ⟨w, (G.mem_neighborSet u w).1 hw, by simpa using hwv⟩
