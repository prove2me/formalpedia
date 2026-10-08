-- Prove2me | solution 1 for UnitCircleCyclicAngleOrder
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:29:36.155671+00:00
-- url     : https://prove2.me/submissions/976a7b1f-910b-4307-b8cb-fedf5714023a

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_UnitCircle
import Definitions.Def_UnitCircleCyclicAngleData
import Theorems.Thm_UnitCircleCyclicAngleBasicOrder
import Theorems.Thm_UnitCircleFundamentalAngles

open Classical
noncomputable section

theorem solution
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : (↑S : Set (EuclideanSpace ℝ (Fin 2))) ⊆ UnitCircle p)
    (hcard : 3 ≤ S.card) :
    Nonempty (UnitCircleCyclicAngleData p S) := by
  rcases UnitCircleFundamentalAngles p S hS with ⟨θ, hθ_mem, hθ_point, hθ_inj⟩
  rcases UnitCircleCyclicAngleBasicOrder p S θ hθ_mem hθ_point hθ_inj hcard with
    ⟨succ, startAngle, endAngle, hsucc_bijective, hsucc_ne, hendpoint_unique,
      hstart_mem, hstart_point, hend_point, hend_lift, hgap_pos, hgap_short,
      hno_S_in_open_gap, hopen_gaps_disjoint⟩
  refine ⟨
    { succ := succ
      startAngle := startAngle
      endAngle := endAngle
      succ_bijective := hsucc_bijective
      succ_ne := hsucc_ne
      endpoint_unique := hendpoint_unique
      start_mem_fundamental := hstart_mem
      start_point := hstart_point
      end_point := hend_point
      end_lift := hend_lift
      gap_pos := hgap_pos
      gap_short := hgap_short
      no_S_in_open_gap := hno_S_in_open_gap
      open_gaps_disjoint := hopen_gaps_disjoint }⟩
