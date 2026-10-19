-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstFiber_diagonalImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/b82fd39c-8755-41c0-b3e0-820702d3c794

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) (x : V) :
    firstFiber (diagonalImage p U) (p x) =
      (firstFiber U x).image (p.prodCongr p) := by
  classical
  ext z
  simp only [firstFiber, diagonalImage, Finset.mem_filter,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, hzw⟩, hzfirst⟩
    refine ⟨w, ⟨hw, ?_⟩, hzw⟩
    apply p.injective
    simpa [← hzw] using hzfirst
  · rintro ⟨w, ⟨hw, hwfirst⟩, hzw⟩
    refine ⟨⟨w, hw, hzw⟩, ?_⟩
    simpa [← hzw] using congrArg p hwfirst
end SoficGroups.KunThomFiberCoarea
