-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_compound_mul_eq_7a2fc1706bba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:23.352878+00:00
-- url     : https://prove2.me/submissions/00fbcad0-056f-4c67-b324-c5c35aa54774

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_one_submatrix_6335cc6abd88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinet_proof_066722d63378


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
theorem _root_.solution {m : ℕ} (B : Matrix (Fin n) (Fin N1) F) (C : Matrix (Fin N1) (Fin n) F) (hBC : B * C = 1)
    (S' S'' : {S : Finset (Fin n) // S.card = m}) :
    ∑ S : {S : Finset (Fin N1) // S.card = m},
        (C.submatrix (S.1.orderEmbOfFin S.2) (S''.1.orderEmbOfFin S''.2)).det *
          (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det =
      if S' = S'' then 1 else 0 := by
  rw [← det_one_submatrix S' S'', ← hBC,
    Matrix.submatrix_mul B C _ id _ Function.bijective_id, CauchyBinet.proof]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
