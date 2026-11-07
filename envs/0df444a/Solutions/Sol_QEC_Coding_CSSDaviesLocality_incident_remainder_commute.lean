-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.incident_remainder_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:43:03.701746+00:00
-- url     : https://prove2.me/submissions/c6ec8c3f-3103-4703-9a06-b48ce14217a9

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_rows_commute

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
theorem _root_.solution (q : ι) : Commute (incidentHamiltonian P Q q) (remainderHamiltonian P Q q) := by
  unfold incidentHamiltonian remainderHamiltonian
  apply Commute.neg_left
  apply Commute.neg_right
  apply Commute.sum_left
  intro j _
  apply Commute.sum_right
  intro k _
  exact rows_commute P Q horth j k
end QEC.Coding.CSSDaviesLocality
