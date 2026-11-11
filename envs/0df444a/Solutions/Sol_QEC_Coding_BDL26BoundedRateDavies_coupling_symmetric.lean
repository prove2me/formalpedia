-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.coupling_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:40:59.157006+00:00
-- url     : https://prove2.me/submissions/924475f0-2bab-4ee6-a51c-19fb3e47127d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_adjoint
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_coupling_adjoint


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    (coupling S n q a).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  exact coupling_adjoint S n q a
end QEC.Coding.BDL26BoundedRateDavies
