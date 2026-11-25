-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_one_submatrix_6335cc6abd88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:26:34.538352+00:00
-- url     : https://prove2.me/submissions/81c35dea-6bf9-4834-8be7-43234700f675

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
theorem _root_.solution {m : ℕ} (S' S'' : {S : Finset (Fin n) // S.card = m}) :
    ((1 : Matrix (Fin n) (Fin n) F).submatrix (S'.1.orderEmbOfFin S'.2) (S''.1.orderEmbOfFin S''.2)).det =
      if S' = S'' then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.submatrix_one _ (S'.1.orderEmbOfFin S'.2).injective, Matrix.det_one]
  · have hsub : ¬ S'.1 ⊆ S''.1 := fun hs =>
      h (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [S'.2, S''.2])))
    obtain ⟨x, hx, hx'⟩ := Finset.not_subset.1 hsub
    have hr : x ∈ Set.range (S'.1.orderEmbOfFin S'.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨r, hr⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne]
    intro he
    apply hx'
    rw [← hr, he]
    exact Finset.orderEmbOfFin_mem _ _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
