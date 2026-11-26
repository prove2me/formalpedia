-- Prove2me | solution 1 for SemigroupBetti.GenData.dg_eq_s_of_s_eq_t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:12:38.339955+00:00
-- url     : https://prove2.me/submissions/bd85cf7b-ce9e-4172-8a56-f93783afabf4

module
public import Definitions.Def_SemigroupBetti_Antichain
public import Definitions.Def_SemigroupBetti_Arith

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (h : G.s = G.t) : G.dg = G.s := by unfold dg; rw [← h, Nat.gcd_self]
end SemigroupBetti.GenData
