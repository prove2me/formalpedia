-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.gibbs_normalized_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:51:52.974776+00:00
-- url     : https://prove2.me/submissions/14978f97-5565-4418-9d42-4bb2d00f5a4c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_normalized_exp


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (β : ℝ) : (gibbs S n β).toOperator =
    (physicalPartition S n β : ℂ)⁻¹ • thermalExponential S n β :=
  CSSGibbs.gibbs_normalized_exp _ _ β
end QEC.Coding.BDL26CSSHamiltonian
