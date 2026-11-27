-- Prove2me | solution 1 for SizeRamsey.c4Transversal_map_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:51.295808+00:00
-- url     : https://prove2.me/submissions/f37b415a-cbcc-4d05-9d07-8dd41e401083

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Theorems.Thm_SizeRamsey_IsC4Map_comp_iso

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {T : Finset W} (hT : c4Transversal H T) :
    c4Transversal G (T.map e.symm.toEquiv.toEmbedding) := by
  intro f hf
  obtain ⟨i, hi⟩ := hT _ (IsC4Map.comp_iso e hf)
  refine ⟨i, Finset.mem_map.mpr ⟨_, hi, ?_⟩⟩
  simp
end SizeRamsey
