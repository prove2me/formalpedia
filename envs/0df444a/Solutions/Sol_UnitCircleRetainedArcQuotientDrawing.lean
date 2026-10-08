-- Prove2me | solution 1 for UnitCircleRetainedArcQuotientDrawing
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:28:42.585987+00:00
-- url     : https://prove2.me/submissions/6e3e3fcd-6d44-4f0a-81e8-f796d6f7609b

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_GeometricArcDrawing
import Definitions.Def_UnitCircle
import Theorems.Thm_UnitCircleRetainedArcDrawingAssembly
import Theorems.Thm_UnitCircleRetainedArcEndpointQuotient

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

theorem solution
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ (ι : Type) (instF : Fintype ι) (instD : DecidableEq ι)
      (A : Finset ι) (endpoint : ι → Sym2 P),
      (A.card : ℝ) =
          ∑ p ∈ P.filter
            (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
            ((P.filter (fun q => q ∈ UnitCircle p)).card : ℝ) ∧
        (∀ i ∈ A, ¬ (endpoint i).IsDiag) ∧
          (∀ e ∈ A.image endpoint,
            (A.filter (fun i => endpoint i = e)).card ≤ 2) ∧
            (∀ (G : SimpleGraph P) [Fintype G.edgeSet],
              G.edgeFinset = A.image endpoint →
                ∃ D : GeometricArcDrawing G,
                  (D.localPairCount : ℝ) ≤ 2 * (P.card : ℝ) ^ 2) := by
  rcases UnitCircleRetainedArcEndpointQuotient P with
    ⟨ι, instF, instD, A, endpoint, center, arcStart, arcEnd, carrier,
      arcInterior, γ, h_card, h_nondiag, h_multiplicity, h_retained,
      h_endpoint_eq, h_endpoints_distinct, h_endpoints_on_circle, h_arc_param,
      h_carrier_circle, h_no_vertex_in_interior, h_same_center_disjoint,
      h_same_center_endpoint_unique⟩
  refine ⟨ι, instF, instD, A, endpoint, h_card, h_nondiag, h_multiplicity, ?_⟩
  exact UnitCircleRetainedArcDrawingAssembly P A endpoint center arcStart arcEnd
    carrier arcInterior γ h_endpoint_eq h_endpoints_distinct h_endpoints_on_circle
    h_arc_param h_carrier_circle h_no_vertex_in_interior h_same_center_disjoint
