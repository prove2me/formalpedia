-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.coupling_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:19:43.914624+00:00
-- url     : https://prove2.me/submissions/9d095253-7c8e-4654-bbe1-2e30b7cdbbc5

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
theorem _root_.solution (q : Physical S n) :
    coupling S n q .y = Complex.I • (Qubit.localX q * Qubit.localZ q) :=
  CSSDaviesLocality.coupling_y q
end QEC.Coding.BDL26CSSDaviesLocality
