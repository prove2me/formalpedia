-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.cocycleEquiv_symm_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:44:40.160204+00:00
-- url     : https://prove2.me/submissions/259c3634-c2b8-4404-885d-b55ad03c34e7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_cocycleEquiv_word
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S n) :
    ((cocycleEquiv S n).symm w).1 = w.1 := by
  have h := cocycleEquiv_word S n ((cocycleEquiv S n).symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm
end QEC.Coding.BDL26LogicalQubitPreservation
