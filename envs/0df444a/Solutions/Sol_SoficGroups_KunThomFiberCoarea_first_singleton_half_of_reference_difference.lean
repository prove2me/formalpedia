-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.first_singleton_half_of_reference_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/fad796af-83ca-445f-a195-a5de7fc61899

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_nonSingletonFirstMultiplicity_le_reference_difference

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
      2 * (singletonSupport (firstMultiplicity U)).card := by
  have hbad := card_nonSingletonFirstMultiplicity_le_reference_difference
    U p
  have hpartition :
      (singletonSupport (firstMultiplicity U)).card +
          (Finset.univ.filter fun x : V =>
            firstMultiplicity U x ≠ 1).card = Fintype.card V := by
    simpa [singletonSupport] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V))
        (fun x => firstMultiplicity U x = 1))
  omega
end SoficGroups.KunThomFiberCoarea
