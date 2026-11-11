-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.incident_card_le_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:32:38.424655+00:00
-- url     : https://prove2.me/submissions/3492a451-08c5-4603-b0bb-7977b6b51c86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_incident_card
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution (q : Physical S n) : (incident S n q).card ≤ 7 := by
  rw [incident_card, Nat.add_comm]
  exact ((state_boundedValence S n).2.2 q).2.2
end QEC.Coding.BDL26CSSHamiltonian
