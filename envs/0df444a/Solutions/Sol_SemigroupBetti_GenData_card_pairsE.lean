-- Prove2me | solution 1 for SemigroupBetti.GenData.card_pairsE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:19:10.975775+00:00
-- url     : https://prove2.me/submissions/4002186c-33d6-44fb-9700-698969e748a1

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_pairsE_injOn

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.pairsE.card = G.E := card_image_of_injOn G.pairsE_injOn
end SemigroupBetti.GenData
