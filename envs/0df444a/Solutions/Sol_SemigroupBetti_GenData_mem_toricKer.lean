-- Prove2me | solution 1 for SemigroupBetti.GenData.mem_toricKer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:59:48.467848+00:00
-- url     : https://prove2.me/submissions/ebcf5179-1aba-4770-9709-def3438fcdd7

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
theorem _root_.solution {f : MvPolynomial (Fin 4) K} : f ∈ G.toricKer K ↔ toricMap K G.n f = 0 :=
  RingHom.mem_ker
end SemigroupBetti.GenData
