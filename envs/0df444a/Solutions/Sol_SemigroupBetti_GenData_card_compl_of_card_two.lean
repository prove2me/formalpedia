-- Prove2me | solution 1 for SemigroupBetti.GenData.card_compl_of_card_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:02:06.898318+00:00
-- url     : https://prove2.me/submissions/775384ce-441c-4c5d-be1a-a093a7add0a2

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {K : Finset (Fin 4)} (hK : K.card = 2) : Kᶜ.card = 2 := by
  rw [card_compl, Fintype.card_fin, hK]
end SemigroupBetti.GenData
