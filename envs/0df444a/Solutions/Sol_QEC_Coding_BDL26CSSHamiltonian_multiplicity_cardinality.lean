-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.multiplicity_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:50:27.496112+00:00
-- url     : https://prove2.me/submissions/defc8a83-c49b-447e-96e0-2fa17ed07ffc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_multiplicity_mul_card_realizable


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution : multiplicity S n * Fintype.card (realizable S n) =
    2 ^ Fintype.card (Physical S n) :=
  CSSGibbs.multiplicity_mul_card_realizable _ _ (row_orthogonal S n)
end QEC.Coding.BDL26CSSHamiltonian
