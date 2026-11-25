-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormLocalization_proof_32fc6cd719d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:14:39.405622+00:00
-- url     : https://prove2.me/submissions/31a23136-1858-42af-9c0a-c044727332da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormLocalization
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_normForm_eq_det_0ca3f0e920b9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace NormFormLocalization
theorem _root_.solution : NormFormLocalization.Statement := by
  intro R F A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n x
  classical
  let b := Module.Free.chooseBasis R A
  let b' := b.localizationLocalization F (nonZeroDivisors R) A'
  have hM : ∀ j, Algebra.leftMulMatrix b' (algebraMap A A' (x j)) =
      (algebraMap R F).mapMatrix (Algebra.leftMulMatrix b (x j)) := fun j =>
    (Algebra.map_leftMulMatrix_localization R (nonZeroDivisors R) b (x j)).symm
  rw [normForm_eq_det b, normForm_eq_det b', RingHom.map_det]
  congr 1
  ext i k
  simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, map_X, map_C]
end NormFormLocalization
end GroundTheory.Heights₂.Heights.Vertical
