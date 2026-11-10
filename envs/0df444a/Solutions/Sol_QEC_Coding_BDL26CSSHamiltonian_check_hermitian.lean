-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.check_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:54:23.207373+00:00
-- url     : https://prove2.me/submissions/d5dbe383-a0f6-42ee-979b-28940a2c791e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_row
attribute [local simp] QEC.Coding.CSSGibbs.hermitian_row



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26RZMap1CoordinateBridge BDL26LevelTwoDecoder
open PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (j : Sum (ZLabel S n) (XLabel S n)) :
    toHermitianQubitOperator (check S n j) = toQubitOperator (check S n j) :=
  CSSGibbs.hermitian_row _ _ j
end QEC.Coding.BDL26CSSHamiltonian
