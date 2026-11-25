-- Prove2me | solution 1 for ShannonColouring.Misses.kempeSwap_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:22:20.421027+00:00
-- url     : https://prove2.me/submissions/9e6e3de2-1201-4b77-874e-2614d95f1db8

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
    (hT : KempeClosed ends s c α γ T) {x : V} (hx : x ∈ T) {δ : Fin k}
    (h : Misses ends s c x (Equiv.swap α γ δ)) : Misses ends s (kempeSwap ends c α γ T) x δ := by
  intro i hi hix
  by_cases hci : c i = α ∨ c i = γ
  · rw [kempeSwap_mem_or hci, if_pos ((hT.mem_of_incident hi hci hix).mp hx)]
    intro heq
    apply h i hi hix
    rw [← heq, Equiv.swap_apply_self]
  · rw [kempeSwap_of_not hci]
    intro heq
    apply h i hi hix
    rw [heq, Equiv.swap_apply_of_ne_of_ne]
    · intro h'; exact hci (Or.inl (heq.trans h'))
    · intro h'; exact hci (Or.inr (heq.trans h'))
end Misses
end ShannonColouring
