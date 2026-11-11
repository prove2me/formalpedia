-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalQubitPreservation.stepRepresentative_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:47:17.809691+00:00
-- url     : https://prove2.me/submissions/b0d80a64-f001-4b29-8fc8-b96c3145e8fd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_cocycleEquiv_word
import Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_cocycleEquiv_symm_word

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26LogicalQubitPreservation
theorem _root_.solution (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    (stepRepresentative S n w).1 = BDL26AlternatingCochain.stepMap1 S n w.1 := by
  rw [stepRepresentative, cocycleEquiv_symm_word,
    BDL26FiniteCohomology.stepCocycle_value, cocycleEquiv_word]
end QEC.Coding.BDL26LogicalQubitPreservation
