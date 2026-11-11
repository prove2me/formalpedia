-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.zero_projector_range_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:26:22.851128+00:00
-- url     : https://prove2.me/submissions/86386547-1251-429f-810d-b296b663e0c9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelled_code_carrier_finrank_two
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_projector_range_labelledCode

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    Module.finrank ℂ (LinearMap.range (projector S n 0)) = 2 := by
  rw [zero_projector_range_labelledCode S n]
  exact labelled_code_carrier_finrank_two S n
end QEC.Coding.BDL26CSSHamiltonian
