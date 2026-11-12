-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logical_class_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:30:29.282644+00:00
-- url     : https://prove2.me/submissions/f3cd04d4-b1b9-4d26-aa5b-481edbe61aa8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_symm_scalar
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalClass S n w = logicalClass S n (prefixRepresentative S n
      (logicalEquiv S n (logicalClass S n w) • BDL26SeedCohomology.seedElement)) := by
  rw [← logicalEquiv_symm_scalar]
  exact ((logicalEquiv S n).symm_apply_apply (logicalClass S n w)).symm
end QEC.Coding.BDL26LogicalQubitPreservation
