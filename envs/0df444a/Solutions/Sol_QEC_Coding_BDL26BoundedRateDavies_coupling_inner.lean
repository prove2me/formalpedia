-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.coupling_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:39:42.719379+00:00
-- url     : https://prove2.me/submissions/8d599607-f23f-4826-b90e-aaf6ed7975a0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_adjoint
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_square
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_coupling_adjoint
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (v w : Qubit.QubitRegister (Physical S n)) :
    inner ℂ (coupling S n q a v) (coupling S n q a w) = inner ℂ v w := by
  have hv : coupling S n q a (coupling S n q a v) = v :=
    congrArg (fun T : Operator (Qubit.QubitRegister (Physical S n)) => T v)
      (coupling_square S n q a)
  calc
    _ = inner ℂ (LinearMap.adjoint (coupling S n q a) (coupling S n q a v)) w :=
      (LinearMap.adjoint_inner_left (coupling S n q a) w (coupling S n q a v)).symm
    _ = inner ℂ v w := by rw [coupling_adjoint, hv]
end QEC.Coding.BDL26BoundedRateDavies
