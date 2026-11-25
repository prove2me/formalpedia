-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjContract_blockIncl_blockEquiv_e7de0e0007e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:34:41.36032+00:00
-- url     : https://prove2.me/submissions/4add0a78-0e75-4bcc-abda-c9579e0e173a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.ProjContract
variable {F : Type u} [Field F] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
namespace GroundTheory.Heights₂.Heights.Targets.ProjContract
theorem _root_.solution (hv : AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    FieldNumbers.blockIncl (emb hv) ι' (blockEquiv hv p) = v p := by
  simp [blockEquiv, Equiv.apply_ofInjective_symm]
end GroundTheory.Heights₂.Heights.Targets.ProjContract
