-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.dissipator_eq_lindblad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:24:06.343539+00:00
-- url     : https://prove2.me/submissions/f95e69ac-4548-436f-bf30-86491982f19d

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
theorem _root_.solution
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) :
    dissipator S n rate = lindbladDissipator (jump S n rate) := rfl
end QEC.Coding.BDL26BoundedRateDavies
