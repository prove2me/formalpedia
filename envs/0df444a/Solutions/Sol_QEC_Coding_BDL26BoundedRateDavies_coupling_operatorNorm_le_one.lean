-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.coupling_operatorNorm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:38:31.669542+00:00
-- url     : https://prove2.me/submissions/fc05bcef-b3f2-44e2-a24c-9add8a525df8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_coupling_operatorNorm_eq_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    operatorNorm (coupling S n q a) ≤ 1 := (coupling_operatorNorm_eq_one S n q a).le
end QEC.Coding.BDL26BoundedRateDavies
