-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_exists_frame_66efb179ad63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:29.006262+00:00
-- url     : https://prove2.me/submissions/26fe25aa-68e2-4254-a60b-10fd13cf37c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaFormulaLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_sq_4c51336df9f8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Set
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.AreaFormulaLocal
namespace GroundTheory.Heights₂.Heights.AreaFormulaLocal
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (W : Submodule ℝ F) {k : ℕ} (hW : finrank ℝ W = k) :
    ∃ (m : ℕ) (c : F →L[ℝ] EuclideanSpace ℝ (Fin k)) (c' : F →L[ℝ] EuclideanSpace ℝ (Fin m)),
      (∀ z, ‖AreaGraphPiece.pairPt (c z) (c' z)‖ = ‖z‖) ∧ ∀ w ∈ W, c' w = 0 := by
  have h1 := (Wᗮ).finrank_add_finrank_orthogonal
  have h2 := W.finrank_add_finrank_orthogonal
  have hK : finrank ℝ (Wᗮᗮ : Submodule ℝ F) = k := by omega
  let b : OrthonormalBasis (Fin k) ℝ (Wᗮᗮ : Submodule ℝ F) :=
    (stdOrthonormalBasis ℝ (Wᗮᗮ : Submodule ℝ F)).reindex (finCongr hK)
  let b' := stdOrthonormalBasis ℝ (Wᗮ : Submodule ℝ F)
  refine ⟨finrank ℝ (Wᗮ : Submodule ℝ F),
    (b.repr.toContinuousLinearEquiv : (Wᗮᗮ : Submodule ℝ F) →L[ℝ] _).comp (Wᗮᗮ).orthogonalProjectionOnto,
    (b'.repr.toContinuousLinearEquiv : (Wᗮ : Submodule ℝ F) →L[ℝ] _).comp (Wᗮ).orthogonalProjectionOnto,
    fun z => ?_, fun w hw => ?_⟩
  · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [AreaGraphPiece.norm_pairPt_sq, Submodule.norm_sq_eq_add_norm_sq_projection z (Wᗮ), add_comm]
    simp
  · have h0 : (Wᗮ).orthogonalProjectionOnto w = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.2 (W.le_orthogonal_orthogonal hw)
    simp [h0]
end GroundTheory.Heights₂.Heights.AreaFormulaLocal
