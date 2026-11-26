-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:17.270878+00:00
-- url     : https://prove2.me/submissions/cda43d36-ea6b-4b69-b487-a62c65efae67

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Theorems.Thm_Scott1976_DataTypesAsLattices_exists_pair


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (u : Pomega) : u ⊆ graph (funOf u) := by
  intro p hp
  obtain ⟨n, m, rfl⟩ := exists_pair p
  exact ⟨n, m, rfl, ⟨n, subset_rfl, hp⟩⟩
end Scott1976.DataTypesAsLattices
