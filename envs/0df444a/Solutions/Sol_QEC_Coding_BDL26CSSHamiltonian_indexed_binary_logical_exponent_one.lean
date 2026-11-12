-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.indexed_binary_logical_exponent_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:59:51.32357+00:00
-- url     : https://prove2.me/submissions/31a19ebb-e5f8-47a7-87a8-28228a067bb8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_binary_logical_exponent_one

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
    Fintype.card (BDL26IndexedDecoder.FamilyQ S depth i) -
      CSSGibbs.checkRank (zSyndrome S i.val) - CSSGibbs.checkRank (xSyndrome S i.val) = 1 :=
  binary_logical_exponent_one S i.val
end QEC.Coding.BDL26CSSHamiltonian
