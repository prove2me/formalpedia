-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstFiber_singletonFirstEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/3acdca6a-30c0-48a1-8034-f7bf650590ab

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
    firstFiber (singletonFirstEdges U) x =
      if firstMultiplicity U x = 1 then firstFiber U x else ∅ := by
  classical
  ext z
  by_cases hz : z.1 = x
  · by_cases hx : firstMultiplicity U x = 1
    · simp [firstFiber, singletonFirstEdges, hz, hx]
    · simp [firstFiber, singletonFirstEdges, hz, hx]
  · by_cases hx : firstMultiplicity U x = 1
    · simp [firstFiber, singletonFirstEdges, hz, hx]
    · simp [firstFiber, singletonFirstEdges, hz, hx]
end SoficGroups.KunThomFiberCoarea
