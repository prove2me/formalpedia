-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:51:08.014411+00:00
-- url     : https://prove2.me/submissions/16df165a-a7d9-4a24-adc1-a9242d3963bd

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
theorem _root_.solution {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {F : X → Matrix ι κ ℂ} {G : X → Matrix κ μ ℂ}
    (hF : ContDiffAt ℝ n F x₀) (hG : ContDiffAt ℝ n G x₀) : ContDiffAt ℝ n (fun x => F x * G x) x₀ := by
  rw [sm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hF i l).mul (hG l j)
end PI.UnitaryGroupMassFormula.UsCost
