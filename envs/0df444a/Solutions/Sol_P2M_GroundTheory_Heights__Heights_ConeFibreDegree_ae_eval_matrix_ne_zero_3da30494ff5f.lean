-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_matrix_ne_zero_3da30494ff5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:53.48292+00:00
-- url     : https://prove2.me/submissions/3c00b16a-8688-4f5c-8e97-af13439a2cd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_ae_eval_ne_zero_univ_4de5667b5aac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_map_curry_volume_16d414f95811


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
open MvPolynomial MeasureTheory Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFibreDegree
namespace GroundTheory.Heights₂.Heights.ConeFibreDegree
theorem _root_.solution {k n : ℕ} (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) :
    ∀ᵐ π : Fin k → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) g ≠ 0 := by
  have hmap : (volume : Measure (Fin k → Fin n → ℂ)) =
      (volume : Measure (Fin k × Fin n → ℂ)).map (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
    rw [ObjectsHeight.map_curry_volume]
    rfl
  rw [hmap, (MeasurableEquiv.curry (Fin k) (Fin n) ℂ).measurableEmbedding.ae_map_iff]
  exact ae_eval_ne_zero_univ g hg
end GroundTheory.Heights₂.Heights.ConeFibreDegree
