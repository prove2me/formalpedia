-- Prove2me | solution 1 for SoficGroups.target_majority_of_small_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/7308cb18-3e5a-4473-9fd3-49ecb607287c

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
    {V : Type*} [DecidableEq V] (C D : Finset V)
    (hsmall : 2 * (C ∆ D).card < C.card) :
    D.card < 2 * (C ∩ D).card := by
  have hC := Finset.card_sdiff_add_card_inter C D
  have hD := Finset.card_sdiff_add_card_inter D C
  have hleft : (C \ D).card ≤ (C ∆ D).card :=
    Finset.card_le_card (Finset.symmDiff_subset_sdiff (s := C) (t := D))
  have hright : (D \ C).card ≤ (C ∆ D).card :=
    Finset.card_le_card (Finset.symmDiff_subset_sdiff' (s := C) (t := D))
  rw [Finset.inter_comm D C] at hD
  omega
end SoficGroups
