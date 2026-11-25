-- Prove2me | solution 1 for ShannonColouring.card_incident_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:03:03.521739+00:00
-- url     : https://prove2.me/submissions/4f8f1179-121a-44b9-ba83-5ba0b8f8c7e4

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
namespace ShannonColouring
theorem _root_.solution (ends : ι → V × V) {s : Finset ι} {e : ι} (he : e ∉ s) {x : V}
    (hex : Incident ends e x) :
    (s.filter fun i => Incident ends i x).card + 1 ≤ degree ends x := by
  have hsub : insert e (s.filter fun i => Incident ends i x) ⊆
      Finset.univ.filter fun i => (ends i).1 = x ∨ (ends i).2 = x := by
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · simpa [Incident] using hex
    · rw [Finset.mem_filter] at hi; simp only [Incident] at hi
      simp [hi.2]
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (fun h => he (Finset.mem_filter.mp h).1)] at this
  exact this
end ShannonColouring
