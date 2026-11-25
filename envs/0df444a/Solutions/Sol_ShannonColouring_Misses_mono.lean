-- Prove2me | solution 1 for ShannonColouring.Misses.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:12:55.109435+00:00
-- url     : https://prove2.me/submissions/7d5d0bac-038b-4321-8248-fdecd199cd31

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
namespace Misses
theorem _root_.solution {s t : Finset ι} {c : ι → Fin k} {x : V} {δ : Fin k}
    (h : Misses ends s c x δ) (hts : t ⊆ s) : Misses ends t c x δ := fun i hi => h i (hts hi)
end Misses
end ShannonColouring
