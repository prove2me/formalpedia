-- Prove2me | solution 1 for ShannonColouring.Misses.kempeSwap_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:21:58.477084+00:00
-- url     : https://prove2.me/submissions/86f73049-1cda-4d52-aaad-774ec3fb807b

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
theorem _root_.solution {s : Finset ι} {c : ι → Fin k} {α γ : Fin k} {T : Set V}
    (hT : KempeClosed ends s c α γ T) {x : V} (hx : x ∉ T) {δ : Fin k}
    (h : Misses ends s c x δ) : Misses ends s (kempeSwap ends c α γ T) x δ := by
  intro i hi hix
  by_cases hci : c i = α ∨ c i = γ
  · rw [kempeSwap_mem_or hci, if_neg (fun h' => hx ((hT.mem_of_incident hi hci hix).mpr h'))]
    exact h i hi hix
  · rw [kempeSwap_of_not hci]
    exact h i hi hix
end Misses
end ShannonColouring
