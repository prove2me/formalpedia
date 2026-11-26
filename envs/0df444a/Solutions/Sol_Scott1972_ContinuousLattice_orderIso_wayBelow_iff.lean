-- Prove2me | solution 1 for Scott1972.ContinuousLattice.orderIso_wayBelow_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:02.748115+00:00
-- url     : https://prove2.me/submissions/fbd98a35-6a38-43e0-a8c5-e2f1854497aa

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_orderIso_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_con_apply
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_min_apply
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition314_fixMap_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition313.con_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition313.min_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition314.fixMap_apply



set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (e : A ≃o B) {x y : A} :
    x ≪ y ↔ e x ≪ e y :=
  ⟨orderIso_wayBelow e, fun h => by
    simpa using orderIso_wayBelow e.symm h⟩
end Scott1972.ContinuousLattice
