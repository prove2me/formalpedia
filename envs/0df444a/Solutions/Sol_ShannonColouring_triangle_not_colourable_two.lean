-- Prove2me | solution 1 for ShannonColouring.triangle_not_colourable_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:54:11.713709+00:00
-- url     : https://prove2.me/submissions/eb00cdb6-2c95-45e6-a661-1b4cadb1c0e6

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : ¬ ∃ c : Fin 3 → Fin 2, IsProperEdgeColouring triangle c := by
  rintro ⟨c, hc⟩
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    refine hc i j hne ?_ hij
    fin_cases i <;> fin_cases j <;> simp only [Incident, triangle] <;> decide
  simpa using Fintype.card_le_of_injective c hinj
end ShannonColouring
