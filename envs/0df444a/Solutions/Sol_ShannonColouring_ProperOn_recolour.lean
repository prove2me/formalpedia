-- Prove2me | solution 1 for ShannonColouring.ProperOn.recolour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:29:39.444794+00:00
-- url     : https://prove2.me/submissions/acf242f7-4241-4ca2-aac1-55d2f9758bca

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_PathEnds
public import Definitions.Def_ShannonColouring_Kempe
public import Theorems.Thm_ShannonColouring_ProperOn_mono
public import Theorems.Thm_ShannonColouring_Misses_mono
public import Theorems.Thm_ShannonColouring_ProperOn_extend

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
variable {V ι : Type*}
variable {ends : ι → V × V} {k : ℕ}
namespace ShannonColouring
namespace ProperOn
theorem _root_.solution [DecidableEq ι] {s : Finset ι} {c : ι → Fin k} (h : ProperOn ends s c) {f : ι}
    (hf : f ∈ s) {δ : Fin k} (hδ : ∀ x, Incident ends f x → Misses ends s c x δ) :
    ProperOn ends s (Function.update c f δ) := by
  have := (h.mono (Finset.erase_subset f s)).extend (Finset.notMem_erase f s)
    ((hδ _ (Or.inl rfl)).mono (Finset.erase_subset f s))
    ((hδ _ (Or.inr rfl)).mono (Finset.erase_subset f s))
  rwa [Finset.insert_erase hf] at this
end ProperOn
end ShannonColouring
