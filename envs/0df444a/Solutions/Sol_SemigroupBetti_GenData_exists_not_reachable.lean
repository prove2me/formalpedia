-- Prove2me | solution 1 for SemigroupBetti.GenData.exists_not_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:59.068889+00:00
-- url     : https://prove2.me/submissions/d675ee7c-a363-4dc7-b301-12c61f79fa47

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_ncomp_le_one_of_reachable

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (h : 2 ≤ G.ncomp d) :
    ∃ z y : G.fiber d, ¬ (G.nabla d).Reachable z y := by
  by_contra hne
  push Not at hne
  have := G.ncomp_le_one_of_reachable hne
  omega
end SemigroupBetti.GenData
