-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logicalStepEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:49:01.873687+00:00
-- url     : https://prove2.me/submissions/f9114f44-cb55-46cd-ae86-12d362dd28e3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalToH1_mk
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_mk
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalStepEquiv S n (logicalClass S n w) =
      logicalClass S (n+1) (stepRepresentative S n w) := by
  apply (logicalToH1 S (n+1)).injective
  change logicalToH1 S (n+1) ((logicalToH1 S (n+1)).symm
    (BDL26FiniteCohomology.stepEquiv S n
      (logicalToH1 S n (logicalClass S n w)))) = _
  rw [LinearEquiv.apply_symm_apply, logicalToH1_mk, BDL26FiniteCohomology.stepEquiv_mk,
    logicalToH1_mk]
  congr 1
end QEC.Coding.BDL26LogicalQubitPreservation
