-- Prove2me | solution 1 for card_valid_bases_eq_numBases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:42.757737+00:00
-- url     : https://prove2.me/submissions/b90e0f73-0f46-4dde-bdbe-05cda437fcef

import Definitions.Def_CARDB
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_CARDB_SmallN
import Theorems.Thm_numBases_eq_filter

set_option autoImplicit true
open Set TopologicalSpace
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
variable {n : ℕ}
theorem _root_.solution (n : ℕ) :
    Fintype.card (ValidBasis (Fin n)) = numBases n := by
  rw [Fintype.card_congr (validBasisEquivMask n), Fintype.card_subtype, numBases_eq_filter]
  refine Finset.card_bij (fun (m : Fin (2 ^ (2 ^ n))) _ => m.val) ?_ ?_ ?_
  · intro m hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr m.isLt, (Finset.mem_filter.mp hm).2⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro m hm
    refine ⟨⟨m, (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hm).2⟩, rfl⟩
