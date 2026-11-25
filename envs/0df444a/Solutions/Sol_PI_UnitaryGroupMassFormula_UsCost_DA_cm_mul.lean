-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.cm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:33.245381+00:00
-- url     : https://prove2.me/submissions/6c29e3a2-ed72-464e-be82-6c306632c8bc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_iff

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}
namespace PI.UnitaryGroupMassFormula.UsCost.DA
theorem _root_.solution {a b c : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} {G : X → Matrix (Fin b) (Fin c) ℂ}
    (hF : ContDiffAt ℝ n F x) (hG : ContDiffAt ℝ n G x) : ContDiffAt ℝ n (fun y => F y * G y) x := by
  rw [cm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hF i l).mul (hG l j)
end PI.UnitaryGroupMassFormula.UsCost.DA
