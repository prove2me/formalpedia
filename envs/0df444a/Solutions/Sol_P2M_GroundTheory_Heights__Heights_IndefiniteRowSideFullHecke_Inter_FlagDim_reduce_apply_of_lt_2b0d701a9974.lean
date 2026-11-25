-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_reduce_apply_of_lt_2b0d701a9974
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:37.204666+00:00
-- url     : https://prove2.me/submissions/bbe234b0-8c23-40bd-9c76-7c6844e813ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_redMat_mul_apply_5b9de35d96d7

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
theorem _root_.solution (T : Matrix (Fin n) (Fin n) K) (hT : ∀ i, (leadBlock T i).det ≠ 0)
    (i c : Fin n) (hc : c < i) : ((1 - redMat T) * T) i c = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, redMat_mul_apply]
  have h1 : Matrix.vecMul (redCoeff T i) (leadBlock T i) = fun c : Fin i.val => T i (Fin.castLE i.2.le c) := by
    rw [redCoeff, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hT i)),
      Matrix.vecMul_one]
  have h2 := congrFun h1 ⟨c.val, hc⟩
  have hcc : (Fin.castLE i.2.le ⟨c.val, hc⟩ : Fin n) = c := Fin.ext rfl
  simp only [Matrix.vecMul, dotProduct, leadBlock, Matrix.submatrix_apply, hcc] at h2
  rw [h2, sub_self]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
