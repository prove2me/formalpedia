-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.coupling_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:20:11.177624+00:00
-- url     : https://prove2.me/submissions/71f78521-8b48-4a35-85f5-b15d2dc7f25b

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
theorem _root_.solution (q : Physical S n) : coupling S n q .z = Qubit.localZ q :=
  CSSDaviesLocality.coupling_z q
end QEC.Coding.BDL26CSSDaviesLocality
