-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.coupling_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:28:57.679365+00:00
-- url     : https://prove2.me/submissions/f8690911-5134-48f0-92ca-26e49aaba3ad

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    coupling S n q a * coupling S n q a = 1 :=
  toHermitianQubitOperator_square (CSSDaviesLocality.singlePauli q a)
end QEC.Coding.BDL26CSSDaviesLocality
