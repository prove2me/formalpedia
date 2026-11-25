-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_formNorm_transpose_mulVec_0c324087ff6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:09.10363+00:00
-- url     : https://prove2.me/submissions/13e36370-8127-47d2-a905-d3fb286ebc8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_euclid_norm_eq_471a80e339c7

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution {S : Matrix (Fin n) (Fin n) ℂ} (hS : IsUnit S) (v : Fin n → ℂ) :
    IndefiniteRowSideFullHecke.ArithBezout.formNorm S (Sᵀ *ᵥ v) = √(IndefiniteRowSideFullHecke.ArithBezout.normSq v) := by
  rw [IndefiniteRowSideFullHecke.ArithBezout.formNorm, mulVec_mulVec, ← transpose_mul,
    mul_nonsing_inv S (isUnit_det_of_isUnit hS), transpose_one, one_mulVec, euclid_norm_eq]
  rfl
end GroundTheory.Heights₂.Heights.ObjectsHeight
