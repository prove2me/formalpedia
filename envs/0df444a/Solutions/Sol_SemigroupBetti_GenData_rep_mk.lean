-- Prove2me | solution 1 for SemigroupBetti.GenData.rep_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:07:12.900557+00:00
-- url     : https://prove2.me/submissions/d442eae0-f87d-4ba5-bb66-e87e97212d79

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (C : (G.nabla d).ConnectedComponent) :
    (G.nabla d).connectedComponentMk (⟨G.rep C, (Quot.out C).2⟩ : G.fiber d) = C :=
  Quot.out_eq C
end SemigroupBetti.GenData
