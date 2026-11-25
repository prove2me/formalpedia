-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_mul_eq_one_1c79c4c51027
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:09.634607+00:00
-- url     : https://prove2.me/submissions/0640fe73-4601-43b4-9c4d-342b8c5bce3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {F : Type} [Field F] {N1 n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (B : Matrix (Fin n) (Fin N1) F) (hB : LinearIndependent F B.row) :
    ∃ C : Matrix (Fin N1) (Fin n) F, B * C = 1 := by
  have hinj : Function.Injective (Matrix.vecMulLinear B) := Matrix.vecMul_injective_iff.2 hB
  obtain ⟨g, hg⟩ := (Matrix.vecMulLinear B).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨Matrix.of fun c b => g (Pi.single c 1) b, ?_⟩
  ext i b
  have hrow : Matrix.vecMulLinear B (Pi.single i 1) = B i := by
    ext c
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have h1 := LinearMap.congr_fun hg (Pi.single i 1)
  rw [LinearMap.comp_apply, hrow, LinearMap.id_apply] at h1
  have h2 : ∑ c, B i c • (Pi.single c 1 : Fin N1 → F) = B i := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  calc (B * Matrix.of fun c b => g (Pi.single c 1) b) i b = ∑ c, B i c * g (Pi.single c 1) b := by
        simp [Matrix.mul_apply]
    _ = g (B i) b := by
        conv_rhs => rw [← h2]
        simp [map_sum, Finset.sum_apply, map_smul]
    _ = (1 : Matrix (Fin n) (Fin n) F) i b := by
        rw [h1, Matrix.one_apply, Pi.single_apply]
        exact if_congr eq_comm rfl rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
