-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.frequency_energyDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:05:30.0652+00:00
-- url     : https://prove2.me/submissions/f6598bb4-bd8a-442f-9deb-886d9ca23371

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Semantics_Davies_actualFrequency_energyDifference


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω * BDL26CSSHamiltonian.hamiltonian S n -
      BDL26CSSHamiltonian.hamiltonian S n *
        actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω =
    (ω : ℂ) • actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
      (coupling S n q a) ω :=
  actualFrequency_energyDifference _ _ _ ω
end QEC.Coding.BDL26CSSDaviesLocality
