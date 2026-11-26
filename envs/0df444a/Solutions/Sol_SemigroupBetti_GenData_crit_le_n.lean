-- Prove2me | solution 1 for SemigroupBetti.GenData.crit_le_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:16:21.19615+00:00
-- url     : https://prove2.me/submissions/a5e59570-6f5d-46f8-88f7-47295c92e57d

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
theorem _root_.solution {i j : Fin 4} (hji : j ≠ i) : G.crit i ≤ G.n j :=
  Nat.find_min' _ (G.isCritCand_n hji)
end SemigroupBetti.GenData
