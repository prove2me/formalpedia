-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.rowSupport_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:02:26.402647+00:00
-- url     : https://prove2.me/submissions/fae9e7d3-0bdc-48c4-adfb-7ff2a313321b

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
theorem _root_.solution (j : Label S n) :
    CSSDaviesLocality.rowSupport (zSyndrome S n) (xSyndrome S n) j =
      checkSupport S n j := rfl
end QEC.Coding.BDL26CSSDaviesLocality
