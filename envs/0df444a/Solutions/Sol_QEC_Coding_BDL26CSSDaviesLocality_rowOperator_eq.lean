-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.rowOperator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:01:24.281607+00:00
-- url     : https://prove2.me/submissions/74657d34-b9aa-450f-b7ee-77684076da28

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
    CSSDaviesLocality.rowOperator (zSyndrome S n) (xSyndrome S n) j =
      toQubitOperator (check S n j) := rfl
end QEC.Coding.BDL26CSSDaviesLocality
