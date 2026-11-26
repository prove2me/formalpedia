-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottExtend_maximal_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:33:36.942485+00:00
-- url     : https://prove2.me/submissions/eeaedecf-4384-483a-8414-7cef811ddf9e

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_eq_sSup_openInfs
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hE : IsContinuousLattice E) (e : X → Y) {g : X → E} {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (h_le : ∀ x, f' (e x) ≤ g x) (y : Y) :
    f' y ≤ scottExtend e g y := by
  rw [continuous_eq_sSup_openInfs hE hf' y]
  refine sSup_le ?_
  rintro d ⟨U, hUo, hyU, rfl⟩
  refine le_trans ?_ (le_sSup ⟨U, hUo, hyU, rfl⟩)
  refine le_sInf ?_
  rintro w ⟨x, hxU, rfl⟩
  exact le_trans (sInf_le ⟨e x, hxU, rfl⟩) (h_le x)
end Scott1972.ContinuousLattice
