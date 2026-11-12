-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.indexedLabelledCode_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:59:29.528635+00:00
-- url     : https://prove2.me/submissions/bd5489e6-18c8-414a-a6d3-20d0c4f734dc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelledCode_carrier

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_118
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_119
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (depth : Nat) (i : LevelIndex depth) :
    (indexedLabelledCode S depth i).carrier =
      ((indexedFamily S depth).complex i).binaryCSSCode.stabilizer.code.carrier :=
  labelledCode_carrier S i.val
end QEC.Coding.BDL26CSSHamiltonian
