-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.cm_updateRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:58:41.827306+00:00
-- url     : https://prove2.me/submissions/33a401e9-bfe6-4c6d-9b44-4602edf34ccb

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
theorem _root_.solution {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (j : Fin a)
    (b : Fin a → ℂ) : ContDiffAt ℝ n (fun y => (F y).updateRow j b) x := by
  rw [cm_iff] at hF ⊢
  intro i l
  by_cases hi : i = j
  · subst hi; simp only [updateRow_self]; exact contDiffAt_const
  · simp only [updateRow_ne hi]; exact hF i l
end PI.UnitaryGroupMassFormula.UsCost.DA
