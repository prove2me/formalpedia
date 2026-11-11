-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.labelled_code_dimension_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:29:19.087291+00:00
-- url     : https://prove2.me/submissions/62d76c19-b7ae-48ca-a1a1-97504729142b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelled_code_carrier_finrank_two

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution : (labelledCode S n).dimension = 2 := by
  rw [QuantumCode.dimension_eq_finrank_carrier]
  exact labelled_code_carrier_finrank_two S n
end QEC.Coding.BDL26CSSHamiltonian
