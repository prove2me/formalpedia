-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_smul_f954aab74cd5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:43.124849+00:00
-- url     : https://prove2.me/submissions/9032cf6f-3291-4145-9b38-7b6eb65787fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm

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
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    {c : ENNReal} (h0 : c ≠ 0) (htop : c ≠ ⊤) : cond (c • μ) s = cond μ s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.restrict_smul, Measure.smul_apply, smul_smul, smul_eq_mul,
    ENNReal.mul_inv (Or.inl h0) (Or.inl htop), mul_comm c⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel h0 htop, mul_one]
end GroundTheory.Heights₂.Heights.ObjectsHeight
