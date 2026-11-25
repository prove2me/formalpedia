-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.hasDerivAt_block_matrix_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:01.215968+00:00
-- url     : https://prove2.me/submissions/29458a57-ecbc-4601-8972-cfdb86dba001

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hd_iff
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
variable {t : ℝ}
namespace PI.UnitaryGroupMassFormula.UsCost.DA
theorem _root_.solution {k j ρ : ℕ} {A11 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A12 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A21 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : ℝ → B.Mat k ρ}
    {A23 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {A32 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {ToralGalois : Matrix (Fin j) (Fin j) ℂ} {cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {B13 : Matrix (Fin j) (Fin j) ℂ} {B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B22 : B.Mat k ρ}
    {B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B31 : Matrix (Fin j) (Fin j) ℂ}
    {B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {B33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : HasDerivAt A11 ToralGalois t) (h12 : HasDerivAt A12 cocyclesToWachVectorsExponent t) (h13 : HasDerivAt A13 B13 t)
    (h21 : HasDerivAt A21 B21 t) (h22 : HasDerivAt A22 B22 t) (h23 : HasDerivAt A23 B23 t)
    (h31 : HasDerivAt A31 B31 t) (h32 : HasDerivAt A32 B32 t) (h33 : HasDerivAt A33 B33 t) :
    HasDerivAt (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y))
      (blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33) t := by
  rw [hd_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
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
