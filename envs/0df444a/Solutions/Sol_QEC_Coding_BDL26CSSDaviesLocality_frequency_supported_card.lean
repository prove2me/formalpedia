-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.frequency_supported_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:05:49.823201+00:00
-- url     : https://prove2.me/submissions/0ef2b36b-0c38-45a5-8ac4-169927109e96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_region_card_le_fifty
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_supported
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
    (subsystem S n q).OperatorSupportedOnRegister
      (actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω) ∧ (subsystem S n q).selected.card ≤ 50 :=
  ⟨frequency_supported S n q a ω, region_card_le_fifty S n q⟩
end QEC.Coding.BDL26CSSDaviesLocality
