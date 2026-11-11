-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.frequency_eq_incident
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:36:39.636202+00:00
-- url     : https://prove2.me/submissions/fc590ff4-7097-48a2-ba5a-da67b29d8336

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_eq_incident
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


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
      (coupling S n q a) ω =
    actualFrequency (incidentHamiltonian S n q) (incidentHamiltonian_symmetric S n q)
      (coupling S n q a) ω :=
  CSSDaviesLocality.frequency_eq_incident (zSyndrome S n) (xSyndrome S n)
    (row_orthogonal S n) q a ω
end QEC.Coding.BDL26CSSDaviesLocality
