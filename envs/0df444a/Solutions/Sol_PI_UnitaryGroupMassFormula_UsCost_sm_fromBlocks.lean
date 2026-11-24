-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sm_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:14.451797+00:00
-- url     : https://prove2.me/submissions/cce16257-6f46-4e03-adf4-c380a4517f0f

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
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι κ' ℂ} {C : X → Matrix ι' κ ℂ} {D : X → Matrix ι' κ' ℂ}
    (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) (hC : ContDiffAt ℝ n C x₀) (hD : ContDiffAt ℝ n D x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x)) x₀ := by
  rw [sm_iff] at hA hB hC hD ⊢
  rintro (i | i) (j | j)
  · simpa only [Matrix.fromBlocks_apply₁₁] using hA i j
  · simpa only [Matrix.fromBlocks_apply₁₂] using hB i j
  · simpa only [Matrix.fromBlocks_apply₂₁] using hC i j
  · simpa only [Matrix.fromBlocks_apply₂₂] using hD i j
end PI.UnitaryGroupMassFormula.UsCost
