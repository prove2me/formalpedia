-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeAreaFormula_hypotheses_inhabited_804a02fb98ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:21:54.519818+00:00
-- url     : https://prove2.me/submissions/8cac0ae2-2beb-4938-b008-2e9e0aef2053

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ae_coordPlaneBlock_det_ne_zero_029df6309a2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreCount_coordPlaneIdeal_b9fcb6704b37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_coordPlaneIdeal_519c239025b6


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
open scoped ENNReal
noncomputable section
variable {m n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ConeAreaFormula
theorem _root_.solution :
    IsProjPrime (coordPlaneIdeal 1 1) ∧ 0 < 1 ∧ 1 ≤ 1 + 1 ∧
      (∀ᵐ π : Fin 1 → Fin (1 + 1) → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std (1 + 1)) (coordPlaneIdeal 1 1) π w ≠ ⊤) ∧
      Measurable (fun _ : EuclideanSpace ℂ (Fin 1) => (1 : ℝ≥0∞)) := by
  refine ⟨isProjPrime_coordPlaneIdeal one_pos 1, one_pos, by norm_num, ?_, measurable_const⟩
  filter_upwards [ae_coordPlaneBlock_det_ne_zero 1 1] with π hπ
  refine Filter.Eventually.of_forall fun w => ?_
  rw [fibreCount_coordPlaneIdeal π hπ w]
  exact ENat.one_ne_top
end ConeAreaFormula
end GroundTheory.Heights₂.Heights
