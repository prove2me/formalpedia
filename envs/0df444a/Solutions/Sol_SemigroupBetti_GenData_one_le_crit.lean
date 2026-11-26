-- Prove2me | solution 1 for SemigroupBetti.GenData.one_le_crit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:00:31.813389+00:00
-- url     : https://prove2.me/submissions/f7ee3430-92ee-4190-a8dd-454604fb1f5d

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_crit_spec

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (i : Fin 4) : 1 ≤ G.crit i := (G.crit_spec i).1
end SemigroupBetti.GenData
