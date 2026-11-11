-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.labelled_code_carrier_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:01:46.590218+00:00
-- url     : https://prove2.me/submissions/cb615570-a70a-4371-b8d1-dd13f1b58046

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_chain_css_carrier_finrank_two
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelledCode_carrier

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    Module.finrank ℂ (labelledCode S n).carrier = 2 := by
  rw [labelledCode_carrier]
  exact chain_css_carrier_finrank_two S n
end QEC.Coding.BDL26CSSHamiltonian
