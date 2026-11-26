-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottTopology_sierpinskiPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:34:09.872796+00:00
-- url     : https://prove2.me/submissions/1dde3755-b1c2-4093-8696-3e9760eb635b

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_9_b
import Theorems.Thm_Scott1972_ContinuousLattice_isContinuousLattice_prop
import Theorems.Thm_Scott1972_ContinuousLattice_scottTopology_prop

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (ι : Type*) :
    (scottTopologicalSpace : TopologicalSpace (ι → Prop)) =
      (inferInstance : TopologicalSpace (ι → Prop)) := by
  rw [proposition_2_9_b (fun _ => Prop) (fun _ => isContinuousLattice_prop)]
  show (@Pi.topologicalSpace ι (fun _ => Prop) (fun _ => scottTopologicalSpace)) =
    @Pi.topologicalSpace ι (fun _ => Prop) (fun _ => sierpinskiSpace)
  congr 1
  funext _
  exact scottTopology_prop
end Scott1972.ContinuousLattice
