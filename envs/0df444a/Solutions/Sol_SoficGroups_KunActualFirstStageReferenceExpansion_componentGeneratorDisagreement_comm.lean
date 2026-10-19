-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/f1b97f0d-307e-49d9-be90-3d14667f88ed

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualFirstStageReferenceExpansion
theorem _root_.solution
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (C : Finset V)
    (σref σact : ι → Equiv.Perm V) :
    componentGeneratorDisagreement C σref σact =
      componentGeneratorDisagreement C σact σref := by
  classical
  unfold componentGeneratorDisagreement
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => ne_comm
end SoficGroups.KunActualFirstStageReferenceExpansion
