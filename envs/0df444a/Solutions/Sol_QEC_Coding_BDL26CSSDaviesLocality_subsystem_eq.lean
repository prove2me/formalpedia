-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.subsystem_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:03:40.558199+00:00
-- url     : https://prove2.me/submissions/65c7eb5a-4e42-4c15-9f8e-e95fc2b3d343

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
    CSSDaviesLocality.subsystem (zSyndrome S n) (xSyndrome S n) q =
      subsystem S n q := rfl
end QEC.Coding.BDL26CSSDaviesLocality
