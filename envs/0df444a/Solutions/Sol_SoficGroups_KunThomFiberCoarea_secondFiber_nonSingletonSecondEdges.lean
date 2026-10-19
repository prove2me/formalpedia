-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.secondFiber_nonSingletonSecondEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/d181cf42-d088-487f-963e-95a26534acde

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
    secondFiber (nonSingletonSecondEdges U) x =
      if secondMultiplicity U x ≠ 1 then secondFiber U x else ∅ := by
  classical
  ext z
  by_cases hz : z.2 = x
  · by_cases hx : secondMultiplicity U x = 1
    · simp [secondFiber, nonSingletonSecondEdges, hz, hx]
    · simp [secondFiber, nonSingletonSecondEdges, hz, hx]
  · by_cases hx : secondMultiplicity U x = 1
    · simp [secondFiber, nonSingletonSecondEdges, hz, hx]
    · simp [secondFiber, nonSingletonSecondEdges, hz, hx]
end SoficGroups.KunThomFiberCoarea
