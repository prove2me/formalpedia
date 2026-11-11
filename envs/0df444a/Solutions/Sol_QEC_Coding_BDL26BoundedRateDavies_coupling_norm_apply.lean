-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.coupling_norm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:52:26.045628+00:00
-- url     : https://prove2.me/submissions/634e08e6-7255-4039-a437-2c4f483ce358

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_coupling_inner

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (v : Qubit.QubitRegister (Physical S n)) : ‖coupling S n q a v‖ = ‖v‖ :=
  ((LinearMap.norm_map_iff_inner_map_map (𝕜 := ℂ) (coupling S n q a)).mpr
    (coupling_inner S n q a)) v
end QEC.Coding.BDL26BoundedRateDavies
