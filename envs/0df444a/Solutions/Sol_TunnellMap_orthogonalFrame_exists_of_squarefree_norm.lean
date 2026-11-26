-- Prove2me | solution 1 for TunnellMap.orthogonalFrame_exists_of_squarefree_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:05.673114+00:00
-- url     : https://prove2.me/submissions/6ae8ca69-ac72-48c8-bb1f-b4025605293c

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Theorems.Thm_TunnellMap_dot_tripleBezout_of_gcd_eq_one
import Theorems.Thm_TunnellMap_tripleGCD_eq_one_of_squarefree_norm
import Theorems.Thm_TunnellMap_orthogonalFrame_exists_of_bezout

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {p : Triple} {n : ℤ}
    (hn : Squarefree n) (hnorm : dot p p = n) :
    Nonempty (OrthogonalFrame p) := by
  have hgcd := tripleGCD_eq_one_of_squarefree_norm hn hnorm
  exact orthogonalFrame_exists_of_bezout (dot_tripleBezout_of_gcd_eq_one hgcd)
end TunnellMap
