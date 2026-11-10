-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteCohomology.stepEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:36:29.685014+00:00
-- url     : https://prove2.me/submissions/855e766e-70a9-48b6-85dc-09436337523b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_rx
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_rz
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_nextEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_nextEquiv_mk


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26FiniteCohomology
theorem _root_.solution (S : OddScale) (n : Nat) (w : Cocycle S n) :
    stepEquiv S n (classOf S n w) = classOf S (n+1) (stepCocycle S n w) := by
  by_cases h : n % 2 = 0
  · rw [stepEquiv_rx S n h]
    exact BDL26RXCohomology.nextEquiv_mk S n (state S n) h w
  · rw [stepEquiv_rz S n h]
    exact BDL26RZCohomology.nextEquiv_mk S n (state S n) h w
end QEC.Coding.BDL26FiniteCohomology
