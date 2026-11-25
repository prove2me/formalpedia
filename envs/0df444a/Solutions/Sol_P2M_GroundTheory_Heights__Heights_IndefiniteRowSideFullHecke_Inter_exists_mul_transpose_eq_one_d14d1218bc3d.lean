-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_mul_transpose_eq_one_d14d1218bc3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:09.411393+00:00
-- url     : https://prove2.me/submissions/369d18e1-60f3-43b7-8afc-a5dcc31cc6dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleDim

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {F : Type} [Field F] {n N : ℕ} (B : Matrix (Fin n) (Fin N) F)
    (hB : LinearIndependent F B) : ∃ D : Matrix (Fin n) (Fin N) F, D * B.transpose = 1 := by
  have hinj : LinearMap.ker B.transpose.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro v w h
    have h' : B.transpose.mulVec v = B.transpose.mulVec w := h
    rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose] at h'
    exact Matrix.vecMul_injective_iff.2 hB h'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hl : Matrix.toLin' B.transpose = B.transpose.mulVecLin := rfl
  rw [← LinearMap.toMatrix'_toLin' B.transpose, ← LinearMap.toMatrix'_comp, hl, hg, LinearMap.toMatrix'_id]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
