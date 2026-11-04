-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixPotential.matrix_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:22:41.495262+00:00
-- url     : https://prove2.me/submissions/c34c243d-5f2b-4acc-88cb-48d68c924b24

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPairs
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPotential
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
namespace ThreeSum.WeightedGlobalArenaPrefixPotential
theorem _root_.solution {r K : ℕ} (x : Index maps τ cap I L R row root Q r K) :
    (M maps τ cap I L R row root).matrix (equiv maps τ cap I L R row root Q r K x)=
      matrix maps τ cap I L R row root Q x := rfl
end ThreeSum.WeightedGlobalArenaPrefixPotential
