-- Prove2me | solution 1 for SoficGroups.KunUniversalGoodRootReferenceCuts.reference_difference_le_symmDiff_add_missing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/648ddf6e-5feb-4884-8b65-288aae6b58df

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUniversalGoodRootReferenceCuts
open scoped symmDiff
namespace SoficGroups.KunUniversalGoodRootReferenceCuts
theorem _root_.solution
    {α : Type*} [DecidableEq α]
    (U T W : Finset α) (hsub : T ⊆ W) :
    (U \ W).card + (W \ U).card ≤
      (U ∆ T).card + (W \ T).card := by
  have hdisjoint : Disjoint (U \ W) (W \ U) :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset
      Finset.sdiff_disjoint
  have htw : (T ∆ W).card = (W \ T).card := by
    rw [Finset.symmDiff_def,
      Finset.sdiff_eq_empty_iff_subset.mpr hsub,
      Finset.empty_union]
  calc
    (U \ W).card + (W \ U).card = (U ∆ W).card := by
      rw [Finset.symmDiff_def,
        Finset.card_union_of_disjoint hdisjoint]
    _ ≤ ((U ∆ T) ∪ (T ∆ W)).card :=
      Finset.card_le_card (symmDiff_triangle U T W)
    _ ≤ (U ∆ T).card + (T ∆ W).card :=
      Finset.card_union_le _ _
    _ = (U ∆ T).card + (W \ T).card := by rw [htw]
end SoficGroups.KunUniversalGoodRootReferenceCuts
