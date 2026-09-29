-- Prove2me | solution 1 for TarchaBraids.presented_relator_conjugate_eq_one_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T07:11:36.591989+00:00
-- url     : https://prove2.me/submissions/09f6a439-7401-45d6-96b4-a786c91c7877

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

open BraidsLinksMCG

theorem solution (n : ℕ)
    (w r : FreeGroup (Fin (n - 1))) (hr : r ∈ braidRels n) :
    PresentedGroup.mk (braidRels n) (w * r * w⁻¹) = 1 := by
  rw [PresentedGroup.mk_eq_one_iff]
  apply Subgroup.conjugatesOfSet_subset_normalClosure
  exact Group.mem_conjugatesOfSet_iff.mpr
    ⟨r, hr, isConj_iff.mpr ⟨w, rfl⟩⟩
