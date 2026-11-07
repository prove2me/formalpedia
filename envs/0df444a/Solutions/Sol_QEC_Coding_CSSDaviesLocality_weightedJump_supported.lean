-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.weightedJump_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:33:27.686689+00:00
-- url     : https://prove2.me/submissions/67059a4c-9e34-4dbd-a765-30296494ca23

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_smul


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
theorem _root_.solution
    (rate : (ι × Axis) → HamiltonianFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q) → ℝ)
    (q : ι) (a : Axis) (ω : HamiltonianFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q)) :
    (subsystem P Q q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian P Q) (hamiltonian_symmetric P Q)
        (fun qa : ι × Axis => coupling qa.1 qa.2) rate ((q,a),ω)) := by
  exact (subsystem P Q q).supported_smul _ (frequency_supported P Q horth q a ω.val)
end QEC.Coding.CSSDaviesLocality
