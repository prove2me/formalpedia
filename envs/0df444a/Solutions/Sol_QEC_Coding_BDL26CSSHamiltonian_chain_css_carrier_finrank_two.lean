-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.chain_css_carrier_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:56:13.832849+00:00
-- url     : https://prove2.me/submissions/571eea93-610b-483a-9983-069df28d2b2d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_homology_finrank_one
import Theorems.Thm_QEC_Coding_ChainComplexData_binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    Module.finrank ℂ (complex S n).binaryCSSCode.stabilizer.code.carrier = 2 := by
  rw [(complex S n).binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology,
    homology_finrank_one]
  norm_num
end QEC.Coding.BDL26CSSHamiltonian
