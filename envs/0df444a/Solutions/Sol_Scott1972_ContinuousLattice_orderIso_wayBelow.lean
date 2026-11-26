-- Prove2me | solution 1 for Scott1972.ContinuousLattice.orderIso_wayBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:37:49.068681+00:00
-- url     : https://prove2.me/submissions/64d7003a-7341-42b4-8424-089b2d64eca4

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
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
theorem _root_.solution (e : A ≃o B) {x y : A} (h : x ≪ y) :
    e x ≪ e y := by
  obtain ⟨U, hU, hyU, hUsub⟩ := h
  refine ⟨e.symm ⁻¹' U, scottOpen_preimage_orderIso e.symm hU, ?_, ?_⟩
  · simpa using hyU
  · intro z hz
    have hxz : x ≤ e.symm z := Set.mem_Ici.1 (hUsub hz)
    exact Set.mem_Ici.2 (by simpa using (e.le_iff_le.mpr hxz))
end Scott1972.ContinuousLattice
