-- Prove2me | solution 1 for PerfectGraphTheorem.isPerfect_compl_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:01:25.164853+00:00
-- url     : https://prove2.me/submissions/977d12af-2566-4e69-bf0b-56596066edb9

module
public import Mathlib
public import Definitions.Def_PerfectLib_Perfect
public import Definitions.Def_PerfectGraphs_Solution
public import Theorems.Thm_PerfectGraph_isPerfect_compl_iff


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PerfectGraphTheorem
variable {V : Type*}
namespace PerfectGraphTheorem
theorem _root_.solution [Finite V] (G : SimpleGraph V) : IsPerfect Gᶜ ↔ IsPerfect G :=
  PerfectGraph.isPerfect_compl_iff G
end PerfectGraphTheorem
