-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.check_card_le_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:36:21.06932+00:00
-- url     : https://prove2.me/submissions/ce71251a-0244-4231-9377-2d112f14a4e0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_z_check_card
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_x_check_card
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (j : Sum (ZLabel S n) (XLabel S n)) : (checkSupport S n j).card ≤ 7 := by
  cases j with
  | inl z => rw [z_check_card]; exact (state_boundedValence S n).2.1 z
  | inr x => rw [x_check_card]; exact (state_boundedValence S n).1 x
end QEC.Coding.BDL26CSSHamiltonian
