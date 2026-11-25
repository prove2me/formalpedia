-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sm_fromRows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:55:58.755782+00:00
-- url     : https://prove2.me/submissions/e9fa27fd-c1c8-4118-bf5a-80ac1d9798f9

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
theorem _root_.solution {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ]
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι' κ ℂ} (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromRows (A x) (B x)) x₀ := by
  rw [sm_iff] at hA hB ⊢
  rintro (i | i) j
  · simpa only [Matrix.fromRows_apply_inl] using hA i j
  · simpa only [Matrix.fromRows_apply_inr] using hB i j
end PI.UnitaryGroupMassFormula.UsCost
