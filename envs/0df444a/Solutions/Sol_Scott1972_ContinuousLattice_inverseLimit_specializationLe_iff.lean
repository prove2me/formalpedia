-- Prove2me | solution 1 for Scott1972.ContinuousLattice.inverseLimit_specializationLe_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:38:01.570237+00:00
-- url     : https://prove2.me/submissions/0f25e28d-1c3b-410e-a570-06c656a9bec8

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_specializationLe_iff_specializes
import Theorems.Thm_Scott1972_ContinuousLattice_specializationLe_scott_iff


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (x y : InverseLimit D P) :
    @SpecializationLe (InverseLimit D P) (inverseLimitTopology D P) x y ↔ x ≤ y := by
  let stageOrder : ∀ n, Preorder (D n) := fun _ => inferInstance
  let limitOrder : Preorder (InverseLimit D P) := inferInstance
  letI : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  letI : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  letI : ∀ n, Preorder (D n) := stageOrder
  letI : Preorder (InverseLimit D P) := limitOrder
  have hval : Topology.IsEmbedding (Subtype.val : InverseLimit D P → ∀ n, D n) :=
    ⟨⟨rfl⟩, Subtype.val_injective⟩
  rw [specializationLe_iff_specializes, ← hval.isInducing.specializes_iff, specializes_pi]
  constructor
  · intro h n
    rw [← specializationLe_scott_iff, specializationLe_iff_specializes]
    exact h n
  · intro h n
    rw [← specializationLe_iff_specializes, specializationLe_scott_iff]
    exact h n
end Scott1972.ContinuousLattice
