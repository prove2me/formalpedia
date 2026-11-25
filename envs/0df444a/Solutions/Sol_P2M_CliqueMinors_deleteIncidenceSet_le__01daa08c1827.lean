-- Prove2me | solution 1 for P2M_CliqueMinors_deleteIncidenceSet_le__01daa08c1827
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:38.616793+00:00
-- url     : https://prove2.me/submissions/a06f98a9-4e87-431e-ba97-c46a6298e39a

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]
namespace CliqueMinors
theorem _root_.solution (G : SimpleGraph V) (v : V) : G.deleteIncidenceSet v ≤ G :=
  fun _ _ h => (deleteIncidenceSet_adj.1 h).1
end CliqueMinors
