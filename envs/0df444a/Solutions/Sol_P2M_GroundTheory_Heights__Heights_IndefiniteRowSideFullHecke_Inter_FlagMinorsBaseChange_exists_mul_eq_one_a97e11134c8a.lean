-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsBaseChange_exists_mul_eq_one_a97e11134c8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:01.63987+00:00
-- url     : https://prove2.me/submissions/25b1a07b-aa32-4f63-823e-6bc59ad68d18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsBaseChange

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMinorsBaseChange
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMinorsBaseChange
theorem _root_.solution {F : Type} [Field F] {n N1 : ℕ} (B : Matrix (Fin n) (Fin N1) F)
    (hB : LinearIndependent F B) : ∃ D : Matrix (Fin N1) (Fin n) F, B * D = 1 := by
  have hinj : Function.Injective B.vecMul := Matrix.vecMul_injective_iff.mpr hB
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective B.vecMulLinear
    (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨(LinearMap.toMatrix' g).transpose, ?_⟩
  rw [Matrix.ext_iff_vecMul]
  intro v
  rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, Matrix.vecMul_one]
  exact congrFun (congrArg DFunLike.coe hg) v
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMinorsBaseChange
