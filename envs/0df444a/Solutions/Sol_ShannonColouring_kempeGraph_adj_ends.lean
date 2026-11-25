-- Prove2me | solution 1 for ShannonColouring.kempeGraph_adj_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:13:35.742077+00:00
-- url     : https://prove2.me/submissions/b4d7acc7-53d0-4922-a506-c8797ec3a906

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_PathEnds
public import Definitions.Def_ShannonColouring_Kempe

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
variable {V ι : Type*}
variable {ends : ι → V × V} {k : ℕ}
namespace ShannonColouring
theorem _root_.solution (hloop : ∀ i, (ends i).1 ≠ (ends i).2) {s : Finset ι}
    {c : ι → Fin k} {α γ : Fin k} {i : ι} (hi : i ∈ s) (hc : c i = α ∨ c i = γ) :
    (kempeGraph ends s c α γ).Adj (ends i).1 (ends i).2 :=
  ⟨hloop i, i, hi, hc, Or.inl ⟨rfl, rfl⟩⟩
end ShannonColouring
