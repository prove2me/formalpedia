-- Prove2me | solution 1 for SemigroupBetti.GenData.single_le_nu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:21.44702+00:00
-- url     : https://prove2.me/submissions/db0671af-5170-4379-b211-3737368ad6e1

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (z : Fin 4 → ℕ) (i : Fin 4) : z i * G.n i ≤ G.nu z := by
  unfold nu
  exact Finset.single_le_sum (f := fun j => z j * G.n j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
end SemigroupBetti.GenData
