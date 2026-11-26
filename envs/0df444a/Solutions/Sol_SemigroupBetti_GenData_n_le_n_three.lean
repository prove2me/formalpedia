-- Prove2me | solution 1 for SemigroupBetti.GenData.n_le_n_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:11.14852+00:00
-- url     : https://prove2.me/submissions/f8c28699-e165-4be3-b443-4ec8f119e81b

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_n_mono

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (i : Fin 4) : G.n i ≤ G.n 3 := G.n_mono (Fin.le_last i)
end SemigroupBetti.GenData
