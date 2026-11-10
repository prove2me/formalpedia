-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.coupling_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:22:27.128426+00:00
-- url     : https://prove2.me/submissions/f5f2401a-341f-4597-becd-3dad57eed13c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_coupling_adjoint


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    LinearMap.adjoint (coupling S n q a) = coupling S n q a :=
  CSSDaviesLocality.coupling_adjoint q a
end QEC.Coding.BDL26CSSDaviesLocality
