-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.coupling_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:23:47.739608+00:00
-- url     : https://prove2.me/submissions/e1638b14-3f1f-4db4-8eb0-3ac48e4dc6c0

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
theorem _root_.solution (q : Physical S n) : coupling S n q .x = Qubit.localX q :=
  CSSDaviesLocality.coupling_x q
end QEC.Coding.BDL26CSSDaviesLocality
