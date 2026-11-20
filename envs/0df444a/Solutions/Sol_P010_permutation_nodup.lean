-- Prove2me | solution 1 for P010.permutation_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:37:34.719782+00:00
-- url     : https://prove2.me/submissions/0bc7d052-237b-46a4-b42e-4aebb21d9501

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (a : List ℕ)
    (ha : IsPermutation n a) : a.Nodup := by
  exact (ha.nodup_iff).2 (List.nodup_range')
end P010
