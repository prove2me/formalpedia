-- Prove2me | solution 1 for Scott1972.ContinuousLattice.IsContinuousLattice.orderIso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:35.188198+00:00
-- url     : https://prove2.me/submissions/959b2dc2-ea3f-446c-99ea-22d28c0f1d5a

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_orderIso_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_con_apply
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_min_apply
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition314_fixMap_apply
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
attribute [local simp] Scott1972.ContinuousLattice.Proposition313.con_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition313.min_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition314.fixMap_apply



set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]
namespace Scott1972.ContinuousLattice
namespace IsContinuousLattice
theorem _root_.solution (e : A ≃o B) (hB : IsContinuousLattice B) :
    IsContinuousLattice A := by
  intro y
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  apply e.le_iff_le.mp
  exact (hB (e y)).2 fun z hz => by
    have hz' : e.symm z ≪ y := by
      simpa using orderIso_wayBelow e.symm hz
    have := hb hz'
    simpa using e.monotone this
end IsContinuousLattice
end Scott1972.ContinuousLattice
