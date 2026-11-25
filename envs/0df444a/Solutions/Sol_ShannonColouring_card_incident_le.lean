-- Prove2me | solution 1 for ShannonColouring.card_incident_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:22:30.385992+00:00
-- url     : https://prove2.me/submissions/b383d9d7-8697-4800-9955-4f7e0f701703

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
theorem _root_.solution (ends : ι → V × V) (s : Finset ι) (x : V) :
    (s.filter fun i => Incident ends i x).card ≤ degree ends x := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi; simp only [Incident] at hi
  simp [hi.2]
end ShannonColouring
