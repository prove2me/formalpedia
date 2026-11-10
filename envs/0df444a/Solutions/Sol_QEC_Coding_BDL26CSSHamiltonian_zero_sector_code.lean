-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.zero_sector_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:27:34.611734+00:00
-- url     : https://prove2.me/submissions/dc15ce29-d282-4004-9b8d-90a3adf971e2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_code_carrier
import Theorems.Thm_QEC_Coding_CSSGibbs_sector_zero_eq_code
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution : sector S n 0 = (complex S n).binaryCSSCode.stabilizer.code.carrier := by
  exact (CSSGibbs.sector_zero_eq_code (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)).trans
    (code_carrier S n)
end QEC.Coding.BDL26CSSHamiltonian
