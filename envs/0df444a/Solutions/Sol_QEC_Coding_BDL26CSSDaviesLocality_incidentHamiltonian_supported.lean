-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.incidentHamiltonian_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:04:28.941776+00:00
-- url     : https://prove2.me/submissions/8fc9025d-47e3-4bf5-aaf5-3b7fb27c0415

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_incidentHamiltonian_supported


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (q : Physical S n) :
    (subsystem S n q).OperatorSupportedOnRegister (incidentHamiltonian S n q) :=
  CSSDaviesLocality.incidentHamiltonian_supported (zSyndrome S n) (xSyndrome S n) q
end QEC.Coding.BDL26CSSDaviesLocality
