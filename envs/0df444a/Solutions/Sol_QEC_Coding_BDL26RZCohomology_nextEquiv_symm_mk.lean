-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.nextEquiv_symm_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:45:03.919075+00:00
-- url     : https://prove2.me/submissions/b58082c3-86df-4a06-8b03-51e2f340548d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_symm_mk
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26RZCohomology.equiv_symm_mk


section
namespace QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
private theorem transport_backward_mk
    (P : TannerSquarePresentation) (D E : ConstructionState) (h : D = E)
    (e : H1 P ≃ₗ[Field] H1 E.presentation)
    (g : Cocycle E.presentation →ₗ[Field] Cocycle P)
    (he : ∀ w, e.symm (classOf E.presentation w) = classOf P (g w))
    (w : Cocycle D.presentation) :
    (Eq.mpr (congrArg (fun T : ConstructionState => H1 P ≃ₗ[Field] H1 T.presentation) h) e).symm
      (classOf D.presentation w) =
    classOf P ((Eq.mpr (congrArg (fun T : ConstructionState =>
      Cocycle T.presentation →ₗ[Field] Cocycle P) h) g) w) := by
  cases h
  exact he w
end QEC.Coding.BDL26RZCohomology
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
namespace QEC.Coding.BDL26RZCohomology
theorem _root_.solution (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) (w : Cocycle (nextState S n C).presentation) :
    (nextEquiv S n C h).symm (classOf (nextState S n C).presentation w) =
      classOf C.presentation (nextBackwardCocycle S n C h w) := by
  exact transport_backward_mk C.presentation (nextState S n C) (rzState S C)
    (show nextState S n C = rzState S C from if_neg h)
    (equiv C.presentation C.admissible C.regular S)
    (backwardCocycle C.presentation C.admissible S)
    (equiv_symm_mk C.presentation C.admissible C.regular S) w
end QEC.Coding.BDL26RZCohomology
