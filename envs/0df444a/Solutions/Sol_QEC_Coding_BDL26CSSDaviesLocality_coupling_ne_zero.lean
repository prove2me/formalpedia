-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.coupling_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:22:41.219855+00:00
-- url     : https://prove2.me/submissions/071ca145-e16c-4502-b20c-458e2abd2ab0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_square

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    coupling S n q a ≠ 0 := by
  intro h
  have hs := coupling_square S n q a
  rw [h, zero_mul] at hs
  exact zero_ne_one hs
end QEC.Coding.BDL26CSSDaviesLocality
