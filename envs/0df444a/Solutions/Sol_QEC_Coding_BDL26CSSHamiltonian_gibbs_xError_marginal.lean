-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.gibbs_xError_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:52:48.035262+00:00
-- url     : https://prove2.me/submissions/f962f2d3-f389-4d65-be12-782abc1ea92a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_pMarginal_trace


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (β : ℝ) (u : LinearMap.range (zSyndrome S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * CSSGibbs.pMarginalProjector (zSyndrome S n) (xSyndrome S n)
        (row_orthogonal S n) u) = (CSSGibbs.rowProbability (zSyndrome S n) (2 * β) u : ℂ) :=
  CSSGibbs.gibbs_pMarginal_trace _ _ (row_orthogonal S n) β u
end QEC.Coding.BDL26CSSHamiltonian
