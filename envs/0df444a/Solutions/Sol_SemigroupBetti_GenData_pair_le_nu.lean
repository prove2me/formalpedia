-- Prove2me | solution 1 for SemigroupBetti.GenData.pair_le_nu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:06:16.509796+00:00
-- url     : https://prove2.me/submissions/23912890-fbad-4c7d-9e47-f006c4778af9

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (y : Fin 4 → ℕ) {k i : Fin 4} (hki : k ≠ i) :
    y k * G.n k + y i * G.n i ≤ G.nu y :=
  Finset.add_le_sum (f := fun j => y j * G.n j) (fun _ _ => Nat.zero_le _)
    (mem_univ k) (mem_univ i) hki
end SemigroupBetti.GenData
