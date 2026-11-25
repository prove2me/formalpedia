-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_redMat_mul_apply_5b9de35d96d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:53.771035+00:00
-- url     : https://prove2.me/submissions/a7868067-eb12-40ed-b5ae-d3985c1981ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
variable {K : Type} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (T : Matrix (Fin n) (Fin n) K) (i c : Fin n) :
    (redMat T * T) i c = ∑ k : Fin i.val, redCoeff T i k * T (Fin.castLE i.2.le k) c := by
  rw [Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE i.2.le) (Fin.castLE_injective _) _ _ ?_ ?_
  · intro k hk
    have hki : ¬ k.val < i.val := fun h => hk ⟨⟨k.val, h⟩, rfl⟩
    simp only [redMat, Matrix.of_apply]
    rw [dif_neg hki, zero_mul]
  · intro k
    simp only [redMat, Matrix.of_apply, Fin.val_castLE]
    rw [dif_pos k.2]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
