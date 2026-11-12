-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.hamiltonian_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:03:52.347694+00:00
-- url     : https://prove2.me/submissions/c4835a2d-39c7-4bb0-a193-be2f9ebcb16b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution :
    CSSDaviesLocality.hamiltonian (zSyndrome S n) (xSyndrome S n) =
      BDL26CSSHamiltonian.hamiltonian S n := rfl
end QEC.Coding.BDL26CSSDaviesLocality
