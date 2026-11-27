-- Prove2me | solution 1 for SizeRamsey.IsC4Map.comp_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:04.012246+00:00
-- url     : https://prove2.me/submissions/f9e809c5-695e-4c4a-a3ea-0f98e599c3e6

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
namespace IsC4Map
theorem _root_.solution
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {f : Fin 4 → V} (hf : IsC4Map G f) :
    IsC4Map H (e ∘ f) := by
  obtain ⟨hinj, h01, h12, h23, h30⟩ := hf
  exact ⟨e.injective.comp hinj, e.map_adj_iff.mpr h01, e.map_adj_iff.mpr h12,
    e.map_adj_iff.mpr h23, e.map_adj_iff.mpr h30⟩
end IsC4Map
end SizeRamsey
