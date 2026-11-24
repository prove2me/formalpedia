-- Prove2me | solution 1 for ULHC.GridIso.mem_image_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:29.568737+00:00
-- url     : https://prove2.me/submissions/ebd00823-72b7-4448-b27c-bc4e075197fc

import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso

set_option autoImplicit true
open ULHC
open Finset
open ULHC.GridIso
variable (I : GridIso)
namespace ULHC.GridIso
theorem _root_.solution {F : Finset Edge} {e : Edge} : I.g e ∈ F.image I.g ↔ e ∈ F := by
  constructor
  · intro h
    obtain ⟨e', he', h'⟩ := Finset.mem_image.1 h
    have : e' = e := by rw [← I.hg e', h', I.hg]
    rwa [← this]
  · exact Finset.mem_image_of_mem _
end ULHC.GridIso
