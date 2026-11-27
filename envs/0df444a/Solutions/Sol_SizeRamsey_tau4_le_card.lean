-- Prove2me | solution 1 for SizeRamsey.tau4_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:18:08.78683+00:00
-- url     : https://prove2.me/submissions/afa7c464-2a6d-4e1f-b486-d7a17060f195

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {S : Finset V}
    (hS : c4Transversal G S) :
    tau4 G ≤ S.card :=
  Nat.sInf_le ⟨S, hS, rfl⟩
end SizeRamsey
