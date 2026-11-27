-- Prove2me | solution 1 for SizeRamsey.tau4_le_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:13.829993+00:00
-- url     : https://prove2.me/submissions/1aab8465-d9e1-4c6f-ac23-7a2e2c8d38ae

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Theorems.Thm_SizeRamsey_tau4_le_card
public import Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4
public import Theorems.Thm_SizeRamsey_c4Transversal_map_iso

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    tau4 G ≤ tau4 H := by
  obtain ⟨T, hT, hcard⟩ := exists_transversal_card_eq_tau4 H
  have := tau4_le_card (c4Transversal_map_iso e hT)
  rwa [Finset.card_map, hcard] at this
end SizeRamsey
