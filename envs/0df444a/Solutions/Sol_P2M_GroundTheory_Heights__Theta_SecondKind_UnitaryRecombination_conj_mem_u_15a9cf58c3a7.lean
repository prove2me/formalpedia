-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_conj_mem_u_15a9cf58c3a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:11:05.760245+00:00
-- url     : https://prove2.me/submissions/b7b69b61-127c-4a34-bce0-7c62db26122d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_GroundTheory_Automorphic_indefJ_conjTranspose


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution {p q : ℕ} {g h X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsU g)
    (hgh : g * h = 1) (hX : X ∈ indefiniteUnitaryLieAlgebra p q) :
    h * X * g ∈ indefiniteUnitaryLieAlgebra p q := by
  rw [mem_indefiniteUnitaryLieAlgebra_iff] at hX ⊢
  unfold IsU at hg
  have e1 : gᴴ * indefJ p q = indefJ p q * h := by
    calc gᴴ * indefJ p q = gᴴ * indefJ p q * (g * h) := by rw [hgh, Matrix.mul_one]
      _ = (gᴴ * indefJ p q * g) * h := by simp only [Matrix.mul_assoc]
      _ = indefJ p q * h := by rw [hg]
  have e2 : hᴴ = indefJ p q * g * indefJ p q := by
    have h3 := congrArg conjTranspose e1
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      indefJ_conjTranspose] at h3
    calc hᴴ = hᴴ * indefJ p q * indefJ p q := by
          rw [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
      _ = indefJ p q * g * indefJ p q := by rw [← h3]
  rw [conjTranspose_mul, conjTranspose_mul, hX, e2]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  rw [J_mul_J_mul, ← Matrix.mul_assoc gᴴ, e1]
  simp only [Matrix.mul_assoc]
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
