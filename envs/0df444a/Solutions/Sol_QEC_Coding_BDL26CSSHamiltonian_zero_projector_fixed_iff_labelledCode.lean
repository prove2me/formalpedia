-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.zero_projector_fixed_iff_labelledCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:58:23.69205+00:00
-- url     : https://prove2.me/submissions/ad363eab-89b7-4504-9d86-42d1bcbe77af

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_labelledCode_carrier
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_projector_code


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (v : Qubit.QubitRegister (Physical S n)) :
    projector S n 0 v = v ↔ v ∈ (labelledCode S n).carrier := by
  rw [labelledCode_carrier S n]
  exact zero_projector_code S n v
end QEC.Coding.BDL26CSSHamiltonian
