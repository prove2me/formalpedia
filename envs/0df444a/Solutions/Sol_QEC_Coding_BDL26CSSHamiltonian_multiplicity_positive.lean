-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.multiplicity_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:50:13.686473+00:00
-- url     : https://prove2.me/submissions/5664662b-b7a3-42b7-89bf-5d361b301a1f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_multiplicity_pos


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution : 0 < multiplicity S n := CSSGibbs.multiplicity_pos _ _
end QEC.Coding.BDL26CSSHamiltonian
