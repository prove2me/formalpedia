-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.contDiffAt_block_matrix_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:31.614066+00:00
-- url     : https://prove2.me/submissions/9ea00c48-236f-423f-868c-4cd7c9ef4ae5

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
theorem _root_.solution {p s : ℕ} {A : X → Matrix (Fin p) (Fin p) ℂ} {B' : X → Matrix (Fin p) (Fin s) ℂ}
    {C : X → Matrix (Fin s) (Fin p) ℂ} {D : X → Matrix (Fin s) (Fin s) ℂ}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B' x) (hC : ContDiffAt ℝ n C x) (hD : ContDiffAt ℝ n D x) :
    ContDiffAt ℝ n (fun y => blk2 (A y) (B' y) (C y) (D y)) x := by
  rw [cm_iff] at hA hB hC hD ⊢
  intro i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂] <;>
    first | exact hA _ _ | exact hB _ _ | exact hC _ _ | exact hD _ _
end PI.UnitaryGroupMassFormula.UsCost.DA
