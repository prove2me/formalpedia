-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.homology_finrank_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:36:03.480737+00:00
-- url     : https://prove2.me/submissions/62f3d851-4e7c-44c3-a167-f95982a1c476

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_cohomology_finrank_one
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_chainComplex_finrank_middleCohomology_eq_middleHomology
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    Module.finrank (ZMod 2) (complex S n).middleHomology = 1 := by
  have h := FiniteFieldPauli.chainComplex_finrank_middleCohomology_eq_middleHomology (complex S n)
  exact h.symm.trans (cohomology_finrank_one S n)
end QEC.Coding.BDL26CSSHamiltonian
