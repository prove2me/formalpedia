-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.secondFiber_diagonalImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/f3d602de-b615-4147-92b0-befd2fbb3540

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) (x : V) :
    secondFiber (diagonalImage p U) (p x) =
      (secondFiber U x).image (p.prodCongr p) := by
  classical
  ext z
  simp only [secondFiber, diagonalImage, Finset.mem_filter,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, hzw⟩, hzsecond⟩
    refine ⟨w, ⟨hw, ?_⟩, hzw⟩
    apply p.injective
    simpa [← hzw] using hzsecond
  · rintro ⟨w, ⟨hw, hwsecond⟩, hzw⟩
    refine ⟨⟨w, hw, hzw⟩, ?_⟩
    simpa [← hzw] using congrArg p hwsecond
end SoficGroups.KunThomFiberCoarea
