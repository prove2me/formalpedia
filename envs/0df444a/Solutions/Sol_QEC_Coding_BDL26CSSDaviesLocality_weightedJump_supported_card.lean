-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.weightedJump_supported_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:06:09.740452+00:00
-- url     : https://prove2.me/submissions/be8bd515-46f9-4fbf-ba6f-8c0155fb76cc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_region_card_le_fifty
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    (subsystem S n q).OperatorSupportedOnRegister
      (hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
      (subsystem S n q).selected.card ≤ 50 :=
  ⟨weightedJump_supported S n rate q a ω, region_card_le_fifty S n q⟩
end QEC.Coding.BDL26CSSDaviesLocality
