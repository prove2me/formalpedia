-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.actual_gibbs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:24:56.421859+00:00
-- url     : https://prove2.me/submissions/830bea38-f410-4d79-8b9a-e9deb66bd1cb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (β : ℝ) :
    (BDL26CSSHamiltonian.gibbs S n β).toOperator =
      (hamiltonianGibbs (BDL26CSSHamiltonian.hamiltonian S n)
        (hamiltonian_symmetric S n) β).toOperator := rfl
end QEC.Coding.BDL26BoundedRateDavies
