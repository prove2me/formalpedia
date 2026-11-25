-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.contDiffAt_block_matrix_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:15.624569+00:00
-- url     : https://prove2.me/submissions/6e826cfa-490a-4254-b0cf-2be4c2afc251

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_apply


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
theorem _root_.solution {k j ρ : ℕ} {A11 : X → Matrix (Fin j) (Fin j) ℂ} {A12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : X → Matrix (Fin j) (Fin j) ℂ} {A21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : X → B.Mat k ρ}
    {A23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : X → Matrix (Fin j) (Fin j) ℂ}
    {A32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : ContDiffAt ℝ n A11 x) (h12 : ContDiffAt ℝ n A12 x) (h13 : ContDiffAt ℝ n A13 x)
    (h21 : ContDiffAt ℝ n A21 x) (h22 : ContDiffAt ℝ n A22 x) (h23 : ContDiffAt ℝ n A23 x)
    (h31 : ContDiffAt ℝ n A31 x) (h32 : ContDiffAt ℝ n A32 x) (h33 : ContDiffAt ℝ n A33 x) :
    ContDiffAt ℝ n (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y)) x := by
  rw [cm_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _
end PI.UnitaryGroupMassFormula.UsCost.DA
