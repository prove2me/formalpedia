-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.swapPoint_swapPoint
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:58.71009+00:00
-- url     : https://prove2.me/submissions/61601a82-b2f7-46b9-a85b-efd6c979bde1

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (z : Point2) : swapPoint (swapPoint z) = z := by
  ext i
  fin_cases i <;> simp [swapPoint, mkPoint2]
