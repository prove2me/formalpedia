-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.conj_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:15:10.518382+00:00
-- url     : https://prove2.me/submissions/863939b7-ed40-4047-8bea-a93d59bb4114

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_embG_exp
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_blockDiag3_smul_middle
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_conj_exp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
section words
variable {k j ρ : ℕ}
private lemma Rn_mul_inv' (x : RC k j ρ) : Rn k j ρ x * (Rn k j ρ x)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have h0 : (Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)) = 0 := by
    ext a b; rcases b with b | b <;> rfl
  simp only [Rn, blk3, Matrix.det_reindex_self]
  rw [h0, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  simp
end words
section comp
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ} {ξ : Xi k p s ρ σ} {Z : G.Mat s}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end comp
end PI.UnitaryGroupMassFormula.UsCost
end
end

set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
variable {k j ρ : ℕ}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (x : RC k j ρ) (Y : B.Mat k ρ) (c : ℂ) :
    (Rn k j ρ x)⁻¹ * embG k j ρ (NormedSpace.exp (c • Y)) * Rn k j ρ x =
      NormedSpace.exp (c • cj k j ρ x Y) := by
  rw [embG_exp, blockDiag3_smul_middle, conj_exp _ _ (Rn_mul_inv' x), Matrix.mul_smul, Matrix.smul_mul]
  rfl
end PI.UnitaryGroupMassFormula.UsCost
