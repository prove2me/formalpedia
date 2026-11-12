-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.zError_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:52:13.063192+00:00
-- url     : https://prove2.me/submissions/7c9d45d0-ffe0-4047-985a-3559240f8a81

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_xSyndrome_transposed


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (e : Word (ZMod 2) (Physical S n)) : xSyndrome S n e =
    BDL26RZMap1CoordinateBridge.tannerCoboundary1
      (BDL26FiniteTannerSquare.transposePresentation (presentation S n)) e := by
  exact DFunLike.congr_fun (xSyndrome_transposed S n) e
end QEC.Coding.BDL26CSSHamiltonian
