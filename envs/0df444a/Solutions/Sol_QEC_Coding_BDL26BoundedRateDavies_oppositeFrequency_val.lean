-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.oppositeFrequency_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:24:02.302983+00:00
-- url     : https://prove2.me/submissions/890b0064-2495-4d0b-b7ea-863104106709

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (ω : BDL26CSSDaviesLocality.Frequency S n) :
    (oppositeFrequency S n ω).val = -ω.val := rfl
end QEC.Coding.BDL26BoundedRateDavies
