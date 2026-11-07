-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.hamiltonian_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:41:45.048831+00:00
-- url     : https://prove2.me/submissions/6310f7cf-5a71-422f-ae47-c421a19802c8

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality

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
theorem _root_.solution (q : ι) : hamiltonian P Q = incidentHamiltonian P Q q + remainderHamiltonian P Q q := by
  unfold hamiltonian incidentHamiltonian remainderHamiltonian
  rw [← neg_add, Finset.sum_add_sum_compl]
end QEC.Coding.CSSDaviesLocality
