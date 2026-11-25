-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.matV_matU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:40:48.964352+00:00
-- url     : https://prove2.me/submissions/a23b4592-69e0-409f-bc03-2166397d2481

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Theorems.Thm_ReciprocityTheory_PGsh_Up_P_fix
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
include hP
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : matV P φ * matU P φ = 1 := by
  have key : ∀ y, (matV P φ * matU P φ) *ᵥ y = y := by
    intro y
    rw [← Matrix.mulVec_mulVec, matU_mulVec, matV_mulVec]
    have e : (⟨P *ᵥ (φ.symm y : Fin g → R), ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) = φ.symm y :=
      Subtype.ext (P_fix P hP _ (φ.symm y).2)
    rw [e, LinearEquiv.apply_symm_apply]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
end ReciprocityTheory.PGsh.Up
