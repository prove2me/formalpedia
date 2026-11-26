-- Prove2me | solution 1 for SemigroupBetti.GenData.card_binomGens_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:10:05.943051+00:00
-- url     : https://prove2.me/submissions/407d7ab7-d996-4eca-b82c-da4d13334a28

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_card_genSet_le

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution : #(G.binomGens K) ≤ G.beta1 := by
  classical
  exact (card_biUnion_le).trans (sum_le_sum fun d _ => G.card_genSet_le K d)
end SemigroupBetti.GenData
