-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.componentGeneratorDisagreement_le_card_mul_component_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/6be32c1c-00bf-420d-b5bc-8a13dcc6936b

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
    (C B : Finset V)
    (σref σact : ι → Equiv.Perm V)
    (hbad : ∀ i (x : V), x ∈ C →
      σref i x ≠ σact i x → x ∈ B) :
    componentGeneratorDisagreement C σref σact ≤
      Fintype.card ι * (C ∩ B).card := by
  classical
  unfold componentGeneratorDisagreement
  calc
    (∑ i : ι, (C.filter fun x => σref i x ≠ σact i x).card) ≤
        ∑ _i : ι, (C ∩ B).card := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.card_le_card
          intro x hx
          obtain ⟨hxC, hdisagree⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_inter.mpr
            ⟨hxC, hbad i x hxC hdisagree⟩
    _ = Fintype.card ι * (C ∩ B).card := by
          simp
end SoficGroups.KunActualFirstStageReferenceExpansion
