-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneSet_hausdorff_null_of_dim_lt_8a4e1c11caea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:50.171194+00:00
-- url     : https://prove2.me/submissions/c14ad4f0-fca0-4a23-8ac2-4d1c5ecffde3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeGraphCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_proof_0af09eb068df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_proof_e2b8f0be35c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NullSmaller_proof_15fa22cfb07c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_proof_60a02c7c6efe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_proof_0dafe800e45e


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
open MvPolynomial MeasureTheory Module
open scoped ENNReal NNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J) = 0 := by
  set g : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.transpose h.mat)⁻¹)
  have hu : IsUnit (Matrix.transpose h.mat).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hsub : coneSet h J ⊆ g '' zeroSetEuc J := by
    intro y hy
    refine ⟨WithLp.toLp 2 (h.pointOf y), hy, ?_⟩
    ext i
    simp [g, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
  calc Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (g '' zeroSetEuc J)
      ≤ (‖g‖₊ : ℝ≥0∞) ^ ((2 * d : ℕ) : ℝ) * Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J) :=
        g.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [NullSmaller.proof n d J hd, mul_zero]
end GroundTheory.Heights₂.Heights
