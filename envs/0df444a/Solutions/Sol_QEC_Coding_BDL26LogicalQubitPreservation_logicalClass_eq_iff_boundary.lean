-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logicalClass_eq_iff_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:44:08.329692+00:00
-- url     : https://prove2.me/submissions/bd26eec1-67ba-4a7c-b5ad-03a1f789fb86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat)
    (u v : DualRepresentative S n) :
    logicalClass S n u = logicalClass S n v ↔
      ∃ f : Word Field (state S n).presentation.X,
        tannerCoboundary0 (state S n).presentation f = fun q => u.1 q - v.1 q := by
  constructor
  · intro h
    have hb := (Submodule.Quotient.eq
      (complex S n).firstCoboundaryInMiddleBoundaryDual).mp h
    change (fun q => u.1 q - v.1 q) ∈ (complex S n).firstCoboundaryCheckCode.carrier at hb
    exact (BDL26RZCohomology.mem_boundary_iff (state S n).presentation _).mp hb
  · intro h
    have hb := (BDL26RZCohomology.mem_boundary_iff (state S n).presentation _).mpr h
    apply (Submodule.Quotient.eq (complex S n).firstCoboundaryInMiddleBoundaryDual).mpr
    exact hb
end QEC.Coding.BDL26LogicalQubitPreservation
