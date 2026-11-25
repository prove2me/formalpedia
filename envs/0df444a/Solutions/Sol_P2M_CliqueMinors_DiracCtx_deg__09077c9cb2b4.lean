-- Prove2me | solution 1 for P2M_CliqueMinors_DiracCtx_deg__09077c9cb2b4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:11.863348+00:00
-- url     : https://prove2.me/submissions/fbfd270c-9506-4f11-be1a-3c7ec4ac4976

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
open CliqueMinors.DiracCtx
variable {G : SimpleGraph V} {S : Finset V}
namespace CliqueMinors.DiracCtx
theorem _root_.solution (H : DiracCtx G S) {v w : V} (h : G.Adj v w) : 3 ≤ G.degree v :=
  H.deg v (H.supp v w h)
end CliqueMinors.DiracCtx
