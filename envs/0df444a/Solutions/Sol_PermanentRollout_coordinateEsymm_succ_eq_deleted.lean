-- Prove2me | solution 1 for PermanentRollout.coordinateEsymm_succ_eq_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/10076799-a274-4c55-996a-71084b539d61

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (u : Fin t → ℂ) (i : Fin t) (q : ℕ) :
    coordinateEsymm u (q + 1) =
      deletedCoordinateEsymm u i (q + 1) +
        u i * deletedCoordinateEsymm u i q := by
  classical
  have hvars :
      ((Finset.univ : Finset (Fin t)).val.map u) =
        u i ::ₘ (((Finset.univ : Finset (Fin t)).erase i).val.map u) := by
    conv_lhs =>
      rw [← Finset.insert_erase (Finset.mem_univ i),
        Finset.insert_val_of_notMem (Finset.notMem_erase i _), Multiset.map_cons]
  simp [coordinateEsymm, deletedCoordinateEsymm, hvars,
    Multiset.esymm, Multiset.map_add, Multiset.map_map,
    Multiset.sum_add, Multiset.sum_map_mul_left]
end PermanentRollout
