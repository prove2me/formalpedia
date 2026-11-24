-- Prove2me | solution 1 for ULHC.GridIso.adj_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:53.481461+00:00
-- url     : https://prove2.me/submissions/2432677e-dd08-4965-8f43-60d36b6a96ad

import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso
import Theorems.Thm_ULHC_Ends_swap


set_option autoImplicit true
open ULHC
open Finset
open ULHC.GridIso
variable (I : GridIso)
namespace ULHC.GridIso
theorem _root_.solution {F : Finset Edge} {u v : Pt} (h : Adj F u v) : Adj (F.image I.g) (I.f u) (I.f v) := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨I.g e, Finset.mem_image_of_mem _ he, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h1, ← h2]
  · exact I.ends e
  · exact (I.ends e).swap
end ULHC.GridIso
