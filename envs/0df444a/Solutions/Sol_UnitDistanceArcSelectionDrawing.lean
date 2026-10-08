-- Prove2me | solution 1 for UnitDistanceArcSelectionDrawing
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:55:12.985714+00:00
-- url     : https://prove2.me/submissions/35b5f0c7-a8a8-4841-8b8a-8c7ac03459d4

import Definitions.Def_GeometricArcDrawing
import Definitions.Def_unitDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Theorems.Thm_EndpointPairMultiplicitySimpleGraph
import Theorems.Thm_UnitCircleRetainedArcQuotientDrawing
import Theorems.Thm_UnitCircleRetainedIncidenceLowerBound

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

theorem solution (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet), ∃ D : GeometricArcDrawing G,
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (D.localPairCount : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by
  classical
  have hretained := UnitCircleRetainedIncidenceLowerBound P
  rcases UnitCircleRetainedArcQuotientDrawing P with
    ⟨ι, instF, instD, A, endpoint, hAcard, h_nondiag, h_multiplicity, hdraw⟩
  letI : Fintype ι := instF
  letI : DecidableEq ι := instD
  rcases EndpointPairMultiplicitySimpleGraph A endpoint h_nondiag h_multiplicity with
    ⟨G, hGfin, hhalf, hEdgeFinset⟩
  letI : Fintype G.edgeSet := hGfin
  rcases hdraw G hEdgeFinset with ⟨D, hlocal⟩
  refine ⟨G, hGfin, D, ?_, hlocal⟩
  have htwice :
      2 * ((unitDist P : ℝ) - (P.card : ℝ)) ≤ (A.card : ℝ) := by
    rw [hAcard]
    linarith [hretained]
  have htoHalf :
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (A.card : ℝ) / 2 := by
    linarith
  exact htoHalf.trans hhalf
