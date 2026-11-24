-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sm_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:16.310799+00:00
-- url     : https://prove2.me/submissions/85d068f8-a055-4ff9-9ff2-813d5b604c9b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_iff

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
theorem _root_.solution {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e₁ : ι ≃ ι') (e₂ : κ ≃ κ') {F : X → Matrix ι κ ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => Matrix.reindex e₁ e₂ (F x)) x₀ := by
  rw [sm_iff] at hF ⊢
  intro i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply] using hF (e₁.symm i) (e₂.symm j)
end PI.UnitaryGroupMassFormula.UsCost
