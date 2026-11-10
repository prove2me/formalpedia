-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.code_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:22:12.558081+00:00
-- url     : https://prove2.me/submissions/69103f28-9d27-48b0-b369-78883e5b9bf8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_xRowCode
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zRowCode

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26RZMap1CoordinateBridge BDL26LevelTwoDecoder
open PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution :
    (binaryCSSStabilizerCodeOfParityChecks (zSyndrome S n) (xSyndrome S n)
      (row_orthogonal S n)).code.carrier = (complex S n).binaryCSSCode.stabilizer.code.carrier := by
  change (binaryStabilizerCommonFixedQuantumCode
    (binaryCSSCheckSet (parityCheckRowCode (xSyndrome S n)) (parityCheckRowCode (zSyndrome S n)))).carrier = _
  rw [xRowCode, zRowCode]
  rfl
end QEC.Coding.BDL26CSSHamiltonian
