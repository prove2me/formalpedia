-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.indexed_projector_range_finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:59:48.092211+00:00
-- url     : https://prove2.me/submissions/5b513b17-5797-4ffb-b013-60abff5e1095

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_projector_range_finrank_two

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
    Module.finrank ℂ (LinearMap.range (projector S i.val 0)) = 2 :=
  zero_projector_range_finrank_two S i.val
end QEC.Coding.BDL26CSSHamiltonian
