-- Prove2me | solution 1 for P010.classConcat_congr_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:40:08.902962+00:00
-- url     : https://prove2.me/submissions/e3d70214-f42b-4492-ba27-4314c5a99787

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (ps qs : List ℕ)
    (hpq : ps.Perm qs) :
    (classConcat n ps).Perm (classConcat n qs) := by
  unfold classConcat
  exact hpq.flatMap_right _
end P010
