-- Prove2me | solution 1 for QEC.Coding.BDL26EvenC4SingleCoordinateLift.chiX_embedC3Input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:04:45.265881+00:00
-- url     : https://prove2.me/submissions/ba0a7e36-44e5-4ca9-bcf1-197972bbbacc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4SingleCoordinateLift
import Theorems.Thm_QEC_Coding_BDL26EvenC4SingleCoordinateLift_deltaX_embedC3Input
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_chiX_top_coefficient
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_residual
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_class_eq_iff_boundary
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_natural
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffixEquiv_self
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffixEquiv_succ


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26EvenC4SingleCoordinateLift
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26AlternatingCochain BDL26OwnerIncidenceMasks
open BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical
namespace QEC.Coding.BDL26EvenC4SingleCoordinateLift
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 1)
    (q : Physical S 3)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex (transposePresentation (state S 3).presentation) q S) :
    BDL26LogicalDefectProtection.chiX S 2 (embedC3Input S u) (rzOldQCoordinate S q v)=
      BDL26LogicalDefectProtection.chiX S 1 u q := by
  let w3 := topCocycle S 1 (input S 1 u) (BDL26ActualFailureReadout.flip S 1 q)
  let w4 := topCocycle S 2 (input S 2 (embedC3Input S u))
    (BDL26ActualFailureReadout.flip S 2 (rzOldQCoordinate S q v))
  obtain ⟨p,hp⟩ := deltaX_embedC3Input S u q v
  have hc : FC.classOf S 4 w4=FC.classOf S 4 (FC.stepCocycle S 3 w3) := by
    apply (class_eq_iff_boundary S 4 w4 (FC.stepCocycle S 3 w3)).mpr
    refine ⟨p,?_⟩
    change tannerCoboundary0 (state S 4).presentation p=
      topWord S 2 (input S 2 (embedC3Input S u)) (BDL26ActualFailureReadout.flip S 2 (rzOldQCoordinate S q v))-
        (FC.stepCocycle S 3 w3).val
    rw [full_residual,FC.stepCocycle_value]
    change tannerCoboundary0 (state S 4).presentation p=
      BDL26LogicalDefectProtection.deltaX S 2 (embedC3Input S u) (rzOldQCoordinate S q v)-
        stepMap1 S 3 (topWord S 1 (input S 1 u) (BDL26ActualFailureReadout.flip S 1 q))
    rw [full_residual,hp]
    abel
  have hstep : suffixEquiv S 2 (1 : LevelIndex 2) (2 : LevelIndex 2)
      (FC.classOf S 3 w3)=FC.stepEquiv S 3 (FC.classOf S 3 w3) := by
    have hs : suffixEquiv S 2 (1 : LevelIndex 2) (2 : LevelIndex 2)
        (FC.classOf S 3 w3)=FC.stepEquiv S 3
          (suffixEquiv S 2 (1 : LevelIndex 2) (1 : LevelIndex 2) (FC.classOf S 3 w3)) :=
      suffixEquiv_succ S 2 (1 : LevelIndex 2) (1 : StepIndex 2) (FC.classOf S 3 w3)
    rw [suffixEquiv_self] at hs
    exact hs
  have hn := coefficient_natural S 2 (1 : LevelIndex 2) (2 : LevelIndex 2)
    (FC.classOf S 3 w3)
  rw [hstep] at hn
  rw [chiX_top_coefficient,chiX_top_coefficient]
  change FC.finiteH1Equiv S 4 (FC.classOf S 4 w4)=
    FC.finiteH1Equiv S 3 (FC.classOf S 3 w3)
  rw [hc,← FC.stepEquiv_mk]
  exact hn
end QEC.Coding.BDL26EvenC4SingleCoordinateLift
