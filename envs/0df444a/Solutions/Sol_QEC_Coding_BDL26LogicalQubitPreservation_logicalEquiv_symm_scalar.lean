-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_symm_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:51:48.633742+00:00
-- url     : https://prove2.me/submissions/eaf7a378-b406-4e80-8ace-f03e4f01c0a2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalToH1_mk
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_symm_scalar
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat) (c : Field) :
    (logicalEquiv S n).symm c = logicalClass S n
      (prefixRepresentative S n (c • BDL26SeedCohomology.seedElement)) := by
  apply (logicalToH1 S n).injective
  change logicalToH1 S n ((logicalToH1 S n).symm
    ((BDL26FiniteCohomology.finiteH1Equiv S n).symm c)) = _
  rw [LinearEquiv.apply_symm_apply, BDL26FiniteCohomology.finiteH1Equiv_symm_scalar,
    logicalToH1_mk]
  congr 1
end QEC.Coding.BDL26LogicalQubitPreservation
