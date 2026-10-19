-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.secondFiber_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/9824c26c-a435-4cf5-a164-065efe011d5f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (U W : Finset (V × V)) (x : V) :
    secondFiber (U \ W) x = secondFiber U x \ secondFiber W x := by
  classical
  ext z
  simp only [secondFiber, Finset.mem_filter, Finset.mem_sdiff]
  aesop
end SoficGroups.KunThomFiberCoarea
