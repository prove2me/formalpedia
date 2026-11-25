-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_realForm_db376f7ec4df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:36.274697+00:00
-- url     : https://prove2.me/submissions/3289332b-9e60-4fe5-bb43-7c5d6dfde3c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PComplexJacobian

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) :
    (realForm A).det = Complex.normSq A.det := by
  let B : Module.Basis (Fin q × Fin 2) ℝ (Fin q → ℂ) :=
    Complex.basisOneI.smulTower' (Pi.basisFun ℂ (Fin q))
  have hM : LinearMap.toMatrix B B ((Matrix.toLin' A).restrictScalars ℝ) = realForm A := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [LinearMap.toMatrix_apply]
    simp only [B, Module.Basis.smulTower'_repr_mk, Module.Basis.smulTower'_apply,
      LinearMap.restrictScalars_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    fin_cases a <;> fin_cases b <;>
      simp [realForm, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hM, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin',
    Algebra.norm_complex_apply]
end GroundTheory.Heights₂.Heights
