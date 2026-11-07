-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.rowSupport_subset_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:56.502311+00:00
-- url     : https://prove2.me/submissions/7e2110a1-3fc7-4c03-9942-70a90d8eb9da

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
theorem _root_.solution (q : ι) {j : Sum κP κQ} (hj : j ∈ incident P Q q) :
    rowSupport P Q j ⊆ region P Q q := by
  intro i hi
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,hi⟩)
end QEC.Coding.CSSDaviesLocality
