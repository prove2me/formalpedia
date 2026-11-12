-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.partition_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:51:11.995371+00:00
-- url     : https://prove2.me/submissions/19bbd797-3bf6-457c-b8fa-81b705e20b03

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_physicalPartition_formula


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (β : ℝ) : physicalPartition S n β =
    multiplicity S n * Real.exp (β * (Fintype.card (ZLabel S n) + Fintype.card (XLabel S n) : Nat)) *
      CSSGibbs.rowPartition (zSyndrome S n) (2 * β) * CSSGibbs.rowPartition (xSyndrome S n) (2 * β) :=
  CSSGibbs.physicalPartition_formula _ _ (row_orthogonal S n) β
end QEC.Coding.BDL26CSSHamiltonian
