-- Prove2me | solution 1 for TunnellMap.Finset.sort_eq_of_sorted_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:19.99081+00:00
-- url     : https://prove2.me/submissions/d0a08d97-04c9-48c4-90da-1d7d88311231

import Mathlib
import Definitions.Def_TunnellMap_KernelArith

set_option autoImplicit true
open TunnellMap
variable {α : Type*}
namespace TunnellMap
namespace Finset
theorem _root_.solution {β : Type*} [LinearOrder β] (s : Finset β)
    (l : List β) (hs : l.Pairwise (· < ·)) (hmem : ∀ x, x ∈ l ↔ x ∈ s) :
    s.sort (· ≤ ·) = l := by
  have hnd : l.Nodup := hs.imp (fun h => ne_of_lt h)
  have hperm : (s.sort (· ≤ ·)).Perm l :=
    (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnd).mpr fun x => by
      rw [Finset.mem_sort, hmem]
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
    (Finset.pairwise_sort _ _) (hs.imp (fun h => le_of_lt h)) hperm
end Finset
end TunnellMap
