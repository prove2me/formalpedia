-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.matU_matV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:34:26.557474+00:00
-- url     : https://prove2.me/submissions/f6a27b86-5e4f-44cc-ace6-d6eb7636a2e3

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Theorems.Thm_ReciprocityTheory_PGsh_Up_matU_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Up_matV_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] {g d : ℕ} (P : Matrix (Fin g) (Fin g) R) (hP : P * P = P)
  (φ : LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R))
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : matU P φ * matV P φ = P := by
  have key : ∀ w, (matU P φ * matV P φ) *ᵥ w = P *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, matV_mulVec, matU_mulVec, LinearEquiv.symm_apply_apply]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
end ReciprocityTheory.PGsh.Up
