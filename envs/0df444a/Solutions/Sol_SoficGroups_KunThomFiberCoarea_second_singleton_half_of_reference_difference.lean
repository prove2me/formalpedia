-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.second_singleton_half_of_reference_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/72e2db51-6088-4359-8696-a227f19c8a5d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_nonSingletonSecondMultiplicity_le_reference_difference

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) (p : Equiv.Perm V)
    (hnear :
      2 * ((U \ SoficGroups.permutationGraph p).card +
        (SoficGroups.permutationGraph p \ U).card) ≤
          Fintype.card V) :
    Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card := by
  have hbad := card_nonSingletonSecondMultiplicity_le_reference_difference
    U p
  have hpartition :
      (singletonSupport (secondMultiplicity U)).card +
          (Finset.univ.filter fun x : V =>
            secondMultiplicity U x ≠ 1).card = Fintype.card V := by
    simpa [singletonSupport] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V))
        (fun x => secondMultiplicity U x = 1))
  omega
end SoficGroups.KunThomFiberCoarea
