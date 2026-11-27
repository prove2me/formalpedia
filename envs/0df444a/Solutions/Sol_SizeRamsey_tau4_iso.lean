-- Prove2me | solution 1 for SizeRamsey.tau4_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:38.782495+00:00
-- url     : https://prove2.me/submissions/fd4a5b84-1286-4535-b86d-911e372c7eab

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Theorems.Thm_SizeRamsey_tau4_le_of_iso

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    tau4 G = tau4 H :=
  le_antisymm (tau4_le_of_iso e) (tau4_le_of_iso e.symm)
end SizeRamsey
