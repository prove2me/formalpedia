-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.checks_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:04:12.633918+00:00
-- url     : https://prove2.me/submissions/01a58dfc-e14b-407d-b0ed-721c8acd254f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_rows_commute


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (j k : Label S n) :
    Commute (toQubitOperator (check S n j)) (toQubitOperator (check S n k)) :=
  CSSDaviesLocality.rows_commute (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n) j k
end QEC.Coding.BDL26CSSDaviesLocality
