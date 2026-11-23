-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.P_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:33.200491+00:00
-- url     : https://prove2.me/submissions/c4e755e3-db21-4af9-9405-1a8d958c0bac

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement

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
theorem _root_.solution (x : Fin g → R) (hx : x ∈ LinearMap.range (Matrix.mulVecLin P)) : P *ᵥ x = x := by
  obtain ⟨w, rfl⟩ := hx
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
end ReciprocityTheory.PGsh.Up
