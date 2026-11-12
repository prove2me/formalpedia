-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.xError_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:51:59.305953+00:00
-- url     : https://prove2.me/submissions/21690a15-8eb0-4b13-b33b-9467522c49c4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (e : Word (ZMod 2) (Physical S n)) : zSyndrome S n e =
    BDL26RZMap1CoordinateBridge.tannerCoboundary1 (presentation S n) e := rfl
end QEC.Coding.BDL26CSSHamiltonian
