-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_eq_iff_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:29:42.514429+00:00
-- url     : https://prove2.me/submissions/3a7f2efd-fabb-4c2d-8b75-18beeac4071b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalClass_eq_iff_boundary

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat)
    (u v : DualRepresentative S n) :
    logicalEquiv S n (logicalClass S n u) = logicalEquiv S n (logicalClass S n v) ↔
      ∃ f : Word Field (state S n).presentation.X,
        tannerCoboundary0 (state S n).presentation f = fun q => u.1 q - v.1 q := by
  constructor
  · intro h
    exact (logicalClass_eq_iff_boundary S n u v).mp ((logicalEquiv S n).injective h)
  · intro h
    exact congrArg (logicalEquiv S n) ((logicalClass_eq_iff_boundary S n u v).mpr h)
end QEC.Coding.BDL26LogicalQubitPreservation
