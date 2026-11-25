-- Prove2me | solution 1 for ShannonColouring.colouring_of_degree_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:02:15.614975+00:00
-- url     : https://prove2.me/submissions/31fecb3e-4eff-4ded-9fd7-310e016e23bc

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
public import Theorems.Thm_ShannonColouring_shannon


set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ 1) :
    ∃ c : ι → Fin 1, IsProperEdgeColouring ends c :=
  shannon ends hloop 1 hΔ
end ShannonColouring
