-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.coupling_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:43:58.687575+00:00
-- url     : https://prove2.me/submissions/0ff6897f-83d8-46bb-a2a8-e9cae8f28645

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_hermitian_pauli_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_mem_region_self

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
omit horth
namespace QEC.Coding.CSSDaviesLocality
theorem _root_.solution (q : ι) (a : Axis) :
    (subsystem P Q q).OperatorSupportedOnRegister (coupling q a) := by
  apply hermitian_pauli_supported
  rw [support_singlePauli, Finset.singleton_subset_iff]
  exact mem_region_self P Q q
end QEC.Coding.CSSDaviesLocality
