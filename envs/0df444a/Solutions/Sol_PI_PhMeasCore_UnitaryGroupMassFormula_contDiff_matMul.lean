-- Prove2me | solution 1 for PI.PhMeasCore.UnitaryGroupMassFormula.contDiff_matMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:17.095206+00:00
-- url     : https://prove2.me/submissions/5c8eab06-8523-45e2-9e8e-a351b260f844

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_ContDiffMulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.PhMeasCore.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} :
    ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a => LinearMap.toContinuousLinearMap
          { toFun := fun b => a * b
            map_add' := fun b c => Matrix.mul_add a b c
            map_smul' := fun r b => by simp }
        map_add' := fun a b => by
          ext c : 1
          simp [Matrix.add_mul]
        map_smul' := fun r a => by
          ext c : 1
          simp }
  have h : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => L p.1 p.2) :=
    L.isBoundedBilinearMap.contDiff
  exact h
end PI.PhMeasCore.UnitaryGroupMassFormula
