-- Prove2me | solution 1 for ShannonColouring.kempeClosed_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:25:17.097677+00:00
-- url     : https://prove2.me/submissions/8a2bc770-6aef-496c-b09f-da51d5a9937b

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_PathEnds
public import Definitions.Def_ShannonColouring_Kempe
public import Theorems.Thm_ShannonColouring_kempeGraph_adj_ends

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
variable {V ι : Type*}
variable {ends : ι → V × V} {k : ℕ}
namespace ShannonColouring
theorem _root_.solution (hloop : ∀ i, (ends i).1 ≠ (ends i).2) {s : Finset ι}
    {c : ι → Fin k} {α γ : Fin k} (z : V) :
    KempeClosed ends s c α γ {x | (kempeGraph ends s c α γ).Reachable z x} := by
  intro i hi hc
  have hadj := kempeGraph_adj_ends hloop hi hc
  exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.reachable.symm⟩
end ShannonColouring
