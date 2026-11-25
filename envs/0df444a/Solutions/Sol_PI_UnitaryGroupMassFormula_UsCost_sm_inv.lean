-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:01.15111+00:00
-- url     : https://prove2.me/submissions/86bea0d7-49a1-4b35-acb5-17cfaffbda60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_det
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_updateRow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀)
    (hu : (F x₀).det ≠ 0) : ContDiffAt ℝ n (fun x => (F x)⁻¹) x₀ := by
  rw [sm_iff]
  intro i l
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((sm_det hF).inv hu).mul (sm_det (sm_updateRow hF l _))
end PI.UnitaryGroupMassFormula.UsCost
