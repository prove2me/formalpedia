-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.nextBackwardCocycle_heq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:52:17.600952+00:00
-- url     : https://prove2.me/submissions/aa7e997e-e889-4be2-9242-87dfb4108177

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
section
namespace QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
private theorem transported_heq {α β : Sort u} (h : α = β) (v : β) :
    HEq (Eq.mpr h v) v := by
  cases h
  rfl
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
    (h : ¬ n % 2 = 0) :
    HEq (nextBackwardCocycle S n C h) (backwardCocycle C.presentation C.admissible S) := by
  exact transported_heq _ _
end QEC.Coding.BDL26RZCohomology
