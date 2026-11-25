-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_blockLinSubst_X_c66491ee9fd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:10.902987+00:00
-- url     : https://prove2.me/submissions/350acc85-6570-47c1-b250-5f45101b7264

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')] {e : K' ≃ K} {A : ∀ k', ι' k' → ι (e k') → F}
open Classical
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
theorem _root_.solution (q : Σ k', ι' k') :
    IsMultiHomog (blockLinSubst e A (X q)) (Pi.single (e q.1) 1) := by
  rw [blockLinSubst_X]
  refine isMultiHomog_sum _ _ fun i _ => ?_
  simpa using isMultiHomog_mul (isMultiHomog_C (ι := ι) (A q.1 q.2 i)) (isMultiHomog_X (e q.1) i)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
