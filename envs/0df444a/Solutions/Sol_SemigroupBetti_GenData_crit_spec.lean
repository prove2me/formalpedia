-- Prove2me | solution 1 for SemigroupBetti.GenData.crit_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:59:02.770669+00:00
-- url     : https://prove2.me/submissions/6b93e871-0f9c-4c31-b64d-99ffb128901d

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (i : Fin 4) : G.IsCritCand i (G.crit i) := Nat.find_spec (G.crit_exists i)
end SemigroupBetti.GenData
