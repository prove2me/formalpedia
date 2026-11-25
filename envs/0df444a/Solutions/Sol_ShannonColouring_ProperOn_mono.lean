-- Prove2me | solution 1 for ShannonColouring.ProperOn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:12:53.397822+00:00
-- url     : https://prove2.me/submissions/2e027afc-fe1c-4e21-a18b-1639b3ea4a8e

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
namespace ProperOn
theorem _root_.solution {s t : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) (hts : t ⊆ s) :
    ProperOn ends t c := fun i hi j hj => h i (hts hi) j (hts hj)
end ProperOn
end ShannonColouring
