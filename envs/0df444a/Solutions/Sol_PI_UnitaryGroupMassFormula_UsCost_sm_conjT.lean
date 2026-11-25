-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sm_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:13.051055+00:00
-- url     : https://prove2.me/submissions/9d00ab5d-a762-4f29-bbba-58c5d77e806f

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] {F : X → Matrix ι κ ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => (F x)ᴴ) x₀ := by
  rw [sm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE.contDiff.contDiffAt).comp x₀ (hF j i)
end PI.UnitaryGroupMassFormula.UsCost
