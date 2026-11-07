-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.frequency_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:44.330204+00:00
-- url     : https://prove2.me/submissions/ac262eea-3235-4f1d-9f87-5742f15bd408

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_incidentHamiltonian_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_coupling_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_eq_incident
import Theorems.Thm_QEC_Semantics_Davies_actualFrequency_supported


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
variable (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
include horth
namespace QEC.Coding.CSSDaviesLocality
theorem _root_.solution (q : ι) (a : Axis) (ω : ℝ) :
    (subsystem P Q q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q) (coupling q a) ω) := by
  rw [frequency_eq_incident P Q horth]
  exact actualFrequency_supported _ _ _ _ (incidentHamiltonian_supported P Q q) (coupling_supported P Q q a) ω
end QEC.Coding.CSSDaviesLocality
