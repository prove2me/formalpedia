-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.exists_nonzero_actualFrequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:38:40.653641+00:00
-- url     : https://prove2.me/submissions/8f677ee0-f8d0-4f1b-b364-3c4bc3b3357d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_ne_zero
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_sum_actualFrequency
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    ∃ ω : Frequency S n,
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : (∑ ω : Frequency S n,
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val) = 0 := Finset.sum_eq_zero (fun ω _ => h ω)
  rw [sum_actualFrequency S n q a] at hz
  exact coupling_ne_zero S n q a hz
end QEC.Coding.BDL26CSSDaviesLocality
