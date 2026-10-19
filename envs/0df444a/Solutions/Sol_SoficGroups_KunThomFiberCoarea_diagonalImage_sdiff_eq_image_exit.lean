-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.diagonalImage_sdiff_eq_image_exit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/14bc6144-2bb6-4160-af58-94a9685c3ef7

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    diagonalImage p U \ U =
      (U.filter fun z => (p.prodCongr p) z ∉ U).image
        (p.prodCongr p) := by
  classical
  ext z
  simp only [diagonalImage, Finset.mem_sdiff, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨w, hw, hzw⟩, hzout⟩
    exact ⟨w, ⟨hw, by simpa [hzw] using hzout⟩, hzw⟩
  · rintro ⟨w, ⟨hw, hwout⟩, hzw⟩
    exact ⟨⟨w, hw, hzw⟩, by simpa [← hzw] using hwout⟩
end SoficGroups.KunThomFiberCoarea
