-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.hamiltonian_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:19:00.562173+00:00
-- url     : https://prove2.me/submissions/828a24ea-c150-4b2e-83f0-21ce35454e4f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution : hamiltonian S n = CSSGibbs.hamiltonian (zSyndrome S n) (xSyndrome S n) := rfl
end QEC.Coding.BDL26CSSHamiltonian
