-- Prove2me | solution 1 for SoficGroups.maximumOverlapPart_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/2ee71142-4a45-45f0-842e-9ef485be93cf

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V)
    (hC : C.Nonempty) (hCU : C ⊆ U) :
    maximumOverlapPart Q C ∈ Q.parts := by
  classical
  have h : C.Nonempty ∧ C ⊆ U := ⟨hC, hCU⟩
  simpa only [maximumOverlapPart, dif_pos h] using
    (exists_maximum_overlap_component Q C hC hCU).choose_spec.1
end SoficGroups
