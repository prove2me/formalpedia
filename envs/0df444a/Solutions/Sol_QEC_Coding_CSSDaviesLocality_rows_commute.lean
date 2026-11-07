-- Prove2me | solution 1 for QEC.Coding.CSSDaviesLocality.rows_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:41.384164+00:00
-- url     : https://prove2.me/submissions/19d11197-c5c8-4e24-a011-1c2712b03f61

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedGroup_pairwise_commutes


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
theorem _root_.solution (j k : Sum κP κQ) : Commute (rowOperator P Q j) (rowOperator P Q k) := by
  let C := binaryCSSStabilizerCodeOfParityChecks P Q horth
  have hm : ∀ l, row P Q l ∈ C.generatedGroup := by
    intro l
    rw [← binaryCSSParityCheckGenerators_generate_generatedGroup P Q horth]
    exact GeneratedStabilizer.generator l
  exact toQubitOperator_commute_of_commutes _ _ (C.generatedGroup_pairwise_commutes (hm j) (hm k))
end QEC.Coding.CSSDaviesLocality
