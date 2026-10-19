-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstFiber_nonSingletonFirstEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/62a8526d-5a33-4d77-9329-b2d4d03dad3f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (U : Finset (V × V)) (x : V) :
    firstFiber (nonSingletonFirstEdges U) x =
      if firstMultiplicity U x ≠ 1 then firstFiber U x else ∅ := by
  classical
  ext z
  by_cases hz : z.1 = x
  · by_cases hx : firstMultiplicity U x = 1
    · simp [firstFiber, nonSingletonFirstEdges, hz, hx]
    · simp [firstFiber, nonSingletonFirstEdges, hz, hx]
  · by_cases hx : firstMultiplicity U x = 1
    · simp [firstFiber, nonSingletonFirstEdges, hz, hx]
    · simp [firstFiber, nonSingletonFirstEdges, hz, hx]
end SoficGroups.KunThomFiberCoarea
