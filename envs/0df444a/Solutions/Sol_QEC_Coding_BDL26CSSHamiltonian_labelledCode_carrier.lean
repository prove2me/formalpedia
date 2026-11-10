-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.labelledCode_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:30:48.381625+00:00
-- url     : https://prove2.me/submissions/3e6e0aa2-3fcc-4e07-882d-035160e53779

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_code_carrier


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    (labelledCode S n).carrier = (complex S n).binaryCSSCode.stabilizer.code.carrier :=
  code_carrier S n
end QEC.Coding.BDL26CSSHamiltonian
