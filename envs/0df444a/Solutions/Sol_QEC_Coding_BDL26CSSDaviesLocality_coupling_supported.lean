-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.coupling_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:04:44.656844+00:00
-- url     : https://prove2.me/submissions/03857de5-5643-4f59-93bb-cd5493338876

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_coupling_supported


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    (subsystem S n q).OperatorSupportedOnRegister (coupling S n q a) :=
  CSSDaviesLocality.coupling_supported (zSyndrome S n) (xSyndrome S n) q a
end QEC.Coding.BDL26CSSDaviesLocality
