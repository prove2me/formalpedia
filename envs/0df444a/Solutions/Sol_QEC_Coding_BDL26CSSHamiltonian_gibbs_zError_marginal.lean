-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.gibbs_zError_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:53:01.737469+00:00
-- url     : https://prove2.me/submissions/e95bf1f6-4116-4b15-bfcb-f532ed30994b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_qMarginal_trace


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (β : ℝ) (v : LinearMap.range (xSyndrome S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * CSSGibbs.qMarginalProjector (zSyndrome S n) (xSyndrome S n)
        (row_orthogonal S n) v) = (CSSGibbs.rowProbability (xSyndrome S n) (2 * β) v : ℂ) :=
  CSSGibbs.gibbs_qMarginal_trace _ _ (row_orthogonal S n) β v
end QEC.Coding.BDL26CSSHamiltonian
