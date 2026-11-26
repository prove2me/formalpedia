-- Prove2me | solution 1 for Scott1972.ContinuousLattice.inverseLimit_t0Space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:37:59.26778+00:00
-- url     : https://prove2.me/submissions/22d0bde7-92e3-4947-a33b-1d103cfbfa37

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_scottTopology_t0Space


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution :
    @T0Space (InverseLimit D P) (inverseLimitTopology D P) := by
  letI : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  letI : ∀ n, T0Space (D n) := fun _ => scottTopology_t0Space
  letI : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  have hval : Topology.IsEmbedding (Subtype.val : InverseLimit D P → ∀ n, D n) :=
    ⟨⟨rfl⟩, Subtype.val_injective⟩
  exact hval.t0Space
end Scott1972.ContinuousLattice
