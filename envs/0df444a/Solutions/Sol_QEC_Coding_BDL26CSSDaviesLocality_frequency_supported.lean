-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.frequency_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:22:46.235291+00:00
-- url     : https://prove2.me/submissions/37875e1e-ac7c-4313-8cb8-2e52a51c276e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
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
        (coupling S n q a) ω) :=
  CSSDaviesLocality.frequency_supported (zSyndrome S n) (xSyndrome S n)
    (row_orthogonal S n) q a ω
end QEC.Coding.BDL26CSSDaviesLocality
