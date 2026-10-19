-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstFiber_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/25a23612-06a1-4270-8b74-f009f4196010

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (U W : Finset (V × V)) (x : V) :
    firstFiber (U \ W) x = firstFiber U x \ firstFiber W x := by
  classical
  ext z
  simp only [firstFiber, Finset.mem_filter, Finset.mem_sdiff]
  aesop
end SoficGroups.KunThomFiberCoarea
