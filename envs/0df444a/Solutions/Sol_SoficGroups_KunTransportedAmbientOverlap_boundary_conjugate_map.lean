-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.boundary_conjugate_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/9cab3901-0a93-4691-a00c-9874578d84b9

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunTransportedAmbientOverlap
theorem _root_.solution
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V)
    (C : Finset V) :
    SoficGroups.boundary
      (fun i => T * σ i * T⁻¹)
      (C.map T.toEmbedding) =
        SoficGroups.boundary σ C := by
  classical
  unfold SoficGroups.boundary
  apply Finset.sum_congr rfl
  intro i _
  have hfilter :
      ((C.map T.toEmbedding).filter fun y =>
        (T * σ i * T⁻¹) y ∉ C.map T.toEmbedding) =
      (C.filter fun x => σ i x ∉ C).map T.toEmbedding := by
    ext y
    simp [Equiv.Perm.mul_apply]
  rw [hfilter, Finset.card_map]
end SoficGroups.KunTransportedAmbientOverlap
