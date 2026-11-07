-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.hermitian_pauli_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:33.424954+00:00
-- url     : https://prove2.me/submissions/9ad5579e-4378-4dd5-ba1b-5ea7fb88d32c

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_pauli_supported
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_smul


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]
namespace QEC.Coding.CSSDaviesLocality
theorem _root_.solution (S : FiniteSubsystem ι) (E : Binary ι)
    (hE : support E ⊆ S.selected) :
    S.OperatorSupportedOnRegister (toHermitianQubitOperator E) :=
  S.supported_smul _ (pauli_supported S E hE)
end QEC.Coding.CSSDaviesLocality
